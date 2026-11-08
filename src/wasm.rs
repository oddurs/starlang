use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item,
    MatchArm, MatchPat, Stmt, StructDecl, TestDecl, Type, UnaryOp,
};

static WASM_RUN_COUNTER: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Clone)]
pub struct WasmArtifact {
    pub bytes: Vec<u8>,
    pub wat: String,
    pub exports: Vec<String>,
    pub code_bytes: usize,
    pub data_bytes: usize,
    pub func_count: usize,
}

#[derive(Debug, Clone)]
pub struct WasmRunReport {
    pub ok: bool,
    pub stdout: String,
    pub tests_passed: usize,
    pub tests_total: usize,
    pub wasm_size_bytes: usize,
    pub duration_ms: u128,
    pub error: Option<String>,
}

/// Zero-dependency RFC 4648 Base64 encoder so `.wasm` binaries can be shipped over JSON
/// to the Web Studio for instant in-browser `WebAssembly.instantiate` execution.
pub fn encode_base64(bytes: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    let mut i = 0usize;
    while i + 3 <= bytes.len() {
        let b0 = bytes[i] as u32;
        let b1 = bytes[i + 1] as u32;
        let b2 = bytes[i + 2] as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(TABLE[((n >> 18) & 0x3F) as usize] as char);
        out.push(TABLE[((n >> 12) & 0x3F) as usize] as char);
        out.push(TABLE[((n >> 6) & 0x3F) as usize] as char);
        out.push(TABLE[(n & 0x3F) as usize] as char);
        i += 3;
    }
    let rem = bytes.len() - i;
    if rem == 1 {
        let n = (bytes[i] as u32) << 16;
        out.push(TABLE[((n >> 18) & 0x3F) as usize] as char);
        out.push(TABLE[((n >> 12) & 0x3F) as usize] as char);
        out.push('=');
        out.push('=');
    } else if rem == 2 {
        let n = ((bytes[i] as u32) << 16) | ((bytes[i + 1] as u32) << 8);
        out.push(TABLE[((n >> 18) & 0x3F) as usize] as char);
        out.push(TABLE[((n >> 12) & 0x3F) as usize] as char);
        out.push(TABLE[((n >> 6) & 0x3F) as usize] as char);
        out.push('=');
    }
    out
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ValType {
    I32,
    I64,
    F64,
}

impl ValType {
    fn byte(self) -> u8 {
        match self {
            ValType::I32 => 0x7F,
            ValType::I64 => 0x7E,
            ValType::F64 => 0x7C,
        }
    }

    fn wat(self) -> &'static str {
        match self {
            ValType::I32 => "i32",
            ValType::I64 => "i64",
            ValType::F64 => "f64",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FuncSig {
    params: Vec<ValType>,
    results: Vec<ValType>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockType {
    Void,
    Val(ValType),
}

impl BlockType {
    fn byte(self) -> u8 {
        match self {
            BlockType::Void => 0x40,
            BlockType::Val(vt) => vt.byte(),
        }
    }

    fn wat(self) -> &'static str {
        match self {
            BlockType::Void => "",
            BlockType::Val(ValType::I32) => " (result i32)",
            BlockType::Val(ValType::I64) => " (result i64)",
            BlockType::Val(ValType::F64) => " (result f64)",
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
enum Instr {
    Unreachable,
    Block(BlockType),
    Loop(BlockType),
    If(BlockType),
    Else,
    End,
    Br(u32),
    BrIf(u32),
    Return,
    Call(u32),
    Drop,
    Select,

    LocalGet(u32),
    LocalSet(u32),
    GlobalGet(u32),
    GlobalSet(u32),

    I32Load(u32),
    I64Load(u32),
    F64Load(u32),
    I32Load8U(u32),
    I32Store(u32),
    I64Store(u32),
    F64Store(u32),
    I32Store8(u32),
    MemorySize,
    MemoryGrow,

    I32Const(i32),
    I64Const(i64),
    F64Const(f64),

    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32GtS,
    I32LeS,
    I32LeU,
    I32GeS,
    I32Add,
    I32Sub,
    I32Mul,
    I32And,
    I32Shl,

    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64GtS,
    I64LeS,
    I64GeS,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64Or,
    I64Shl,
    I64ShrU,

    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,
    F64Abs,
    F64Neg,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,

    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
}

struct DefinedFunc {
    name: String,
    export_name: Option<String>,
    sig: FuncSig,
    extra_locals: Vec<ValType>,
    body: Vec<Instr>,
}

struct ImportFunc {
    module: &'static str,
    field: &'static str,
    wat_name: &'static str,
    sig: FuncSig,
}

// Fixed host imports (`0..=6`)
const FN_IMP_PRINT_I64: u32 = 0;
const FN_IMP_PRINT_F64: u32 = 1;
const FN_IMP_PRINT_BOOL: u32 = 2;
const FN_IMP_PRINT_STR: u32 = 3;
const FN_IMP_PRINT_SEP: u32 = 4;
const FN_IMP_PRINT_NL: u32 = 5;
const FN_IMP_TOSTR_F64: u32 = 6;

// Fixed native Wasm runtime functions (`7..=20`)
const FN_ALLOC: u32 = 7;
const FN_I64_MIN: u32 = 8;
const FN_I64_MAX: u32 = 9;
const FN_I64_ABS: u32 = 10;
const FN_STR_EQ: u32 = 11;
const FN_STR_CONCAT: u32 = 12;
const FN_STR_CONTAINS: u32 = 13;
const FN_STR_UPPER: u32 = 14;
const FN_STR_LOWER: u32 = 15;
const FN_I64_TO_STR: u32 = 16;
const FN_BOOL_TO_STR: u32 = 17;
const FN_LIST_NEW: u32 = 18;
const FN_LIST_PUSH_SLOT: u32 = 19;
const FN_LIST_SLOT_ADDR: u32 = 20;

const BASE_DATA_OFFSET: u32 = 64;

/// Compile a `HubModule` directly to W3C WebAssembly 1.0 binary bytecode (`.wasm`)
/// and symbolic WebAssembly Text (`.wat`) with zero external crates.
pub fn compile_wasm(hub: &HubModule) -> Result<WasmArtifact, String> {
    let mut compiler = WasmCompiler::new(hub);
    compiler.compile()
}

/// Compile `hub` to `.wasm` and execute `main` + all `test_*` exports inside V8's
/// native WebAssembly JIT (`node` `WebAssembly.instantiate`).
pub fn run_wasm_jit(hub: &HubModule) -> WasmRunReport {
    let start = Instant::now();
    let artifact = match compile_wasm(hub) {
        Ok(a) => a,
        Err(e) => {
            return WasmRunReport {
                ok: false,
                stdout: String::new(),
                tests_passed: 0,
                tests_total: 0,
                wasm_size_bytes: 0,
                duration_ms: start.elapsed().as_millis(),
                error: Some(format!("Wasm compile error: {}", e)),
            };
        }
    };

    let wasm_size_bytes = artifact.bytes.len();
    let run_id = WASM_RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir: PathBuf = std::env::temp_dir().join(format!(
        "starlang_wasm_{}_{}",
        std::process::id(),
        run_id
    ));
    if let Err(e) = fs::create_dir_all(&dir) {
        return WasmRunReport {
            ok: false,
            stdout: String::new(),
            tests_passed: 0,
            tests_total: 0,
            wasm_size_bytes,
            duration_ms: start.elapsed().as_millis(),
            error: Some(e.to_string()),
        };
    }

    let wasm_path = dir.join("module.wasm");
    let runner_path = dir.join("run_wasm.mjs");

    if let Err(e) = fs::write(&wasm_path, &artifact.bytes) {
        let _ = fs::remove_dir_all(&dir);
        return WasmRunReport {
            ok: false,
            stdout: String::new(),
            tests_passed: 0,
            tests_total: 0,
            wasm_size_bytes,
            duration_ms: start.elapsed().as_millis(),
            error: Some(e.to_string()),
        };
    }

    let mjs = r#"import fs from "node:fs";

const wasmBytes = fs.readFileSync(new URL("./module.wasm", import.meta.url));
const decoder = new TextDecoder("utf-8");
const encoder = new TextEncoder();
let memory = null;
let allocFn = null;
let outBuf = "";

const imports = {
  env: {
    print_i64(v) { outBuf += v.toString(); },
    print_f64(v) { outBuf += (Object.is(v, -0) ? "0" : String(v)); },
    print_bool(v) { outBuf += (v !== 0 ? "true" : "false"); },
    print_str(packed) {
      const u = BigInt.asUintN(64, packed);
      const ptr = Number(u & 0xffffffffn);
      const len = Number(u >> 32n);
      const bytes = new Uint8Array(memory.buffer, ptr, len);
      outBuf += decoder.decode(bytes);
    },
    print_sep() { outBuf += " "; },
    print_nl() { outBuf += "\n"; },
    tostr_f64(v) {
      const s = Object.is(v, -0) ? "0" : String(v);
      const bytes = encoder.encode(s);
      const ptr = allocFn(bytes.length) >>> 0;
      new Uint8Array(memory.buffer, ptr, bytes.length).set(bytes);
      return BigInt(ptr) | (BigInt(bytes.length) << 32n);
    },
  },
};

const { instance } = await WebAssembly.instantiate(wasmBytes, imports);
memory = instance.exports.memory;
allocFn = instance.exports.__star_alloc;

if (typeof instance.exports.main === "function") {
  instance.exports.main();
}
const mainStdout = outBuf;

let passed = 0;
let total = 0;
const failures = [];
for (const [name, fn] of Object.entries(instance.exports)) {
  if (name.startsWith("test_") && typeof fn === "function") {
    total += 1;
    try {
      fn();
      passed += 1;
    } catch (err) {
      failures.push(`${name}: ${err && err.message ? err.message : String(err)}`);
    }
  }
}

process.stdout.write(mainStdout);
if (failures.length > 0) {
  process.stderr.write(`WASM_META:${passed}/${total}|FAIL:${failures.join("; ")}\n`);
  process.exit(1);
} else {
  process.stderr.write(`WASM_META:${passed}/${total}|OK\n`);
}
"#;

    let _ = fs::write(&runner_path, mjs);
    let out = Command::new("node")
        .arg("--no-warnings")
        .arg(&runner_path)
        .output();
    let _ = fs::remove_dir_all(&dir);

    match out {
        Ok(res) => {
            let stdout = String::from_utf8_lossy(&res.stdout).to_string();
            let stderr = String::from_utf8_lossy(&res.stderr).to_string();
            let mut tests_passed = 0usize;
            let mut tests_total = 0usize;
            let mut fail_detail = None;

            for line in stderr.lines() {
                if let Some(rest) = line.strip_prefix("WASM_META:") {
                    if let Some((counts, status)) = rest.split_once('|') {
                        if let Some((p, t)) = counts.split_once('/') {
                            tests_passed = p.parse().unwrap_or(0);
                            tests_total = t.parse().unwrap_or(0);
                        }
                        if let Some(f) = status.strip_prefix("FAIL:") {
                            fail_detail = Some(f.to_string());
                        }
                    }
                }
            }

            let ok = res.status.success();
            let error = if ok {
                None
            } else {
                fail_detail.or_else(|| Some(stderr.trim().to_string()))
            };

            WasmRunReport {
                ok,
                stdout,
                tests_passed,
                tests_total,
                wasm_size_bytes,
                duration_ms: start.elapsed().as_millis(),
                error,
            }
        }
        Err(e) => WasmRunReport {
            ok: false,
            stdout: String::new(),
            tests_passed: 0,
            tests_total: 0,
            wasm_size_bytes,
            duration_ms: start.elapsed().as_millis(),
            error: Some(format!("failed to invoke node V8 Wasm runner: {}", e)),
        },
    }
}

struct WasmCompiler<'a> {
    hub: &'a HubModule,
    imports: Vec<ImportFunc>,
    defined: Vec<DefinedFunc>,
    data: Vec<u8>,
    interned_strings: HashMap<String, i64>,
    packed_true: i64,
    packed_false: i64,

    structs: HashMap<String, &'a StructDecl>,
    enums: HashMap<String, HashMap<String, i64>>,
    user_fn_indices: HashMap<String, u32>,
    user_fn_sigs: HashMap<String, (Vec<Type>, Type)>,
    struct_eq_fns: HashMap<String, u32>,
    list_eq_fns: HashMap<Type, u32>,
    list_contains_fns: HashMap<Type, u32>,
}

impl<'a> WasmCompiler<'a> {
    fn new(hub: &'a HubModule) -> Self {
        let imports = vec![
            ImportFunc {
                module: "env",
                field: "print_i64",
                wat_name: "print_i64",
                sig: FuncSig {
                    params: vec![ValType::I64],
                    results: vec![],
                },
            },
            ImportFunc {
                module: "env",
                field: "print_f64",
                wat_name: "print_f64",
                sig: FuncSig {
                    params: vec![ValType::F64],
                    results: vec![],
                },
            },
            ImportFunc {
                module: "env",
                field: "print_bool",
                wat_name: "print_bool",
                sig: FuncSig {
                    params: vec![ValType::I32],
                    results: vec![],
                },
            },
            ImportFunc {
                module: "env",
                field: "print_str",
                wat_name: "print_str",
                sig: FuncSig {
                    params: vec![ValType::I64],
                    results: vec![],
                },
            },
            ImportFunc {
                module: "env",
                field: "print_sep",
                wat_name: "print_sep",
                sig: FuncSig {
                    params: vec![],
                    results: vec![],
                },
            },
            ImportFunc {
                module: "env",
                field: "print_nl",
                wat_name: "print_nl",
                sig: FuncSig {
                    params: vec![],
                    results: vec![],
                },
            },
            ImportFunc {
                module: "env",
                field: "tostr_f64",
                wat_name: "tostr_f64",
                sig: FuncSig {
                    params: vec![ValType::F64],
                    results: vec![ValType::I64],
                },
            },
        ];

        let mut comp = Self {
            hub,
            imports,
            defined: Vec::new(),
            data: Vec::new(),
            interned_strings: HashMap::new(),
            packed_true: 0,
            packed_false: 0,
            structs: HashMap::new(),
            enums: HashMap::new(),
            user_fn_indices: HashMap::new(),
            user_fn_sigs: HashMap::new(),
            struct_eq_fns: HashMap::new(),
            list_eq_fns: HashMap::new(),
            list_contains_fns: HashMap::new(),
        };

        comp.packed_true = comp.intern_str("true");
        comp.packed_false = comp.intern_str("false");
        comp
    }

    fn intern_str(&mut self, s: &str) -> i64 {
        if let Some(&packed) = self.interned_strings.get(s) {
            return packed;
        }
        let ptr = BASE_DATA_OFFSET + self.data.len() as u32;
        let bytes = s.as_bytes();
        self.data.extend_from_slice(bytes);
        let len = bytes.len() as u32;
        let packed = ((ptr as u64) | ((len as u64) << 32)) as i64;
        self.interned_strings.insert(s.to_string(), packed);
        packed
    }

    fn val_type_of(&self, ty: &Type) -> Result<Option<ValType>, String> {
        match ty {
            Type::Void => Ok(None),
            Type::Int => Ok(Some(ValType::I64)),
            Type::Float => Ok(Some(ValType::F64)),
            Type::Bool => Ok(Some(ValType::I32)),
            Type::Str => Ok(Some(ValType::I64)),
            Type::List(_) => Ok(Some(ValType::I32)),
            Type::Named(n) => {
                if self.enums.contains_key(n) {
                    Ok(Some(ValType::I64))
                } else if self.structs.contains_key(n) {
                    Ok(Some(ValType::I32))
                } else {
                    Err(format!("unknown type '{}' in Wasm backend", n))
                }
            }
        }
    }

    fn slot_val_type(&self, ty: &Type) -> Result<ValType, String> {
        self.val_type_of(ty)?
            .ok_or_else(|| "cannot store Void value in Wasm slot".to_string())
    }

    fn next_func_idx(&self) -> u32 {
        (self.imports.len() + self.defined.len()) as u32
    }

    fn compile(&mut self) -> Result<WasmArtifact, String> {
        // 1. Register enums & structs
        for item in &self.hub.items {
            match item {
                Item::Enum(e) => {
                    let mut map = HashMap::new();
                    for (idx, v) in e.variants.iter().enumerate() {
                        map.insert(v.clone(), idx as i64);
                    }
                    self.enums.insert(e.name.clone(), map);
                }
                Item::Struct(s) => {
                    self.structs.insert(s.name.clone(), s);
                }
                _ => {}
            }
        }

        // 2. Emit fixed native Wasm runtime functions (`7..=20`)
        self.emit_runtime_functions();

        // 3. Reserve function indices for struct deep-equality helpers
        let struct_names: Vec<String> = self
            .hub
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Struct(s) => Some(s.name.clone()),
                _ => None,
            })
            .collect();
        for sname in &struct_names {
            let idx = self.next_func_idx();
            self.struct_eq_fns.insert(sname.clone(), idx);
            self.defined.push(DefinedFunc {
                name: format!("eq_struct_{}", sname),
                export_name: None,
                sig: FuncSig {
                    params: vec![ValType::I32, ValType::I32],
                    results: vec![ValType::I32],
                },
                extra_locals: Vec::new(),
                body: Vec::new(),
            });
        }

        // 4. Reserve function indices for all user functions and tests (supports mutual recursion)
        let mut fn_slots: Vec<(usize, &'a FnDecl)> = Vec::new();
        let mut test_slots: Vec<(usize, &'a TestDecl)> = Vec::new();
        for item in &self.hub.items {
            match item {
                Item::Function(f) => {
                    let mut ptypes = Vec::with_capacity(f.params.len());
                    let mut htypes = Vec::with_capacity(f.params.len());
                    for p in &f.params {
                        ptypes.push(self.slot_val_type(&p.ty)?);
                        htypes.push(p.ty.clone());
                    }
                    let results = match self.val_type_of(&f.ret_ty)? {
                        Some(vt) => vec![vt],
                        None => vec![],
                    };
                    let fidx = self.next_func_idx();
                    let def_slot = self.defined.len();
                    self.user_fn_indices.insert(f.name.clone(), fidx);
                    self.user_fn_sigs
                        .insert(f.name.clone(), (htypes, f.ret_ty.clone()));
                    let export_name = Some(f.name.clone());
                    self.defined.push(DefinedFunc {
                        name: f.name.clone(),
                        export_name,
                        sig: FuncSig {
                            params: ptypes,
                            results,
                        },
                        extra_locals: Vec::new(),
                        body: Vec::new(),
                    });
                    fn_slots.push((def_slot, f));
                }
                Item::Test(t) => {
                    let def_slot = self.defined.len();
                    let export_name = format!("test_{}", t.name);
                    self.defined.push(DefinedFunc {
                        name: export_name.clone(),
                        export_name: Some(export_name),
                        sig: FuncSig {
                            params: vec![],
                            results: vec![],
                        },
                        extra_locals: Vec::new(),
                        body: Vec::new(),
                    });
                    test_slots.push((def_slot, t));
                }
                Item::Struct(_) | Item::Enum(_) => {}
            }
        }

        // 5. Fill struct deep-equality bodies (may recursively request list equality helpers)
        for sname in &struct_names {
            let sdecl = self.structs[sname];
            let def_slot = (*self.struct_eq_fns.get(sname).unwrap() as usize) - self.imports.len();
            let body = self.build_struct_eq_body(sdecl)?;
            self.defined[def_slot].body = body;
        }

        // 6. Compile user functions & unit tests
        for (def_slot, fdecl) in fn_slots {
            let (extra_locals, body) = self.compile_fn_body(fdecl)?;
            self.defined[def_slot].extra_locals = extra_locals;
            self.defined[def_slot].body = body;
        }
        for (def_slot, tdecl) in test_slots {
            let (extra_locals, body) = self.compile_test_body(tdecl)?;
            self.defined[def_slot].extra_locals = extra_locals;
            self.defined[def_slot].body = body;
        }

        // 7. Encode W3C Wasm 1.0 binary & symbolic `.wat`
        Ok(self.encode_module())
    }

    fn ensure_list_eq_fn(&mut self, elem_ty: &Type) -> Result<u32, String> {
        if let Some(&idx) = self.list_eq_fns.get(elem_ty) {
            return Ok(idx);
        }
        let idx = self.next_func_idx();
        let def_slot = self.defined.len();
        self.list_eq_fns.insert(elem_ty.clone(), idx);
        let elem_vt = self.slot_val_type(elem_ty)?;
        self.defined.push(DefinedFunc {
            name: format!("eq_list_{}", mangle_type(elem_ty)),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I32, ValType::I32],
                results: vec![ValType::I32],
            },
            // locals: 0=a, 1=b, 2=len(i32), 3=i(i32), 4=da(i32), 5=db(i32)
            extra_locals: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            body: Vec::new(),
        });

        let mut b = vec![
            // if a == b return 1
            Instr::LocalGet(0),
            Instr::LocalGet(1),
            Instr::I32Eq,
            Instr::If(BlockType::Void),
            Instr::I32Const(1),
            Instr::Return,
            Instr::End,
            // len = load_i32(a + 4); if len != load_i32(b + 4) return 0
            Instr::LocalGet(0),
            Instr::I32Load(4),
            Instr::LocalSet(2),
            Instr::LocalGet(2),
            Instr::LocalGet(1),
            Instr::I32Load(4),
            Instr::I32Ne,
            Instr::If(BlockType::Void),
            Instr::I32Const(0),
            Instr::Return,
            Instr::End,
            // da = load_i32(a), db = load_i32(b), i = 0
            Instr::LocalGet(0),
            Instr::I32Load(0),
            Instr::LocalSet(4),
            Instr::LocalGet(1),
            Instr::I32Load(0),
            Instr::LocalSet(5),
            Instr::I32Const(0),
            Instr::LocalSet(3),
            Instr::Block(BlockType::Void),
            Instr::Loop(BlockType::Void),
            Instr::LocalGet(3),
            Instr::LocalGet(2),
            Instr::I32GeS,
            Instr::BrIf(1),
            // load element from da + i*8
            Instr::LocalGet(4),
            Instr::LocalGet(3),
            Instr::I32Const(3),
            Instr::I32Shl,
            Instr::I32Add,
            load_slot_instr(elem_vt, 0),
            // load element from db + i*8
            Instr::LocalGet(5),
            Instr::LocalGet(3),
            Instr::I32Const(3),
            Instr::I32Shl,
            Instr::I32Add,
            load_slot_instr(elem_vt, 0),
        ];
        self.emit_val_eq_instrs(elem_ty, &mut b)?;
        b.extend([
            Instr::I32Eqz,
            Instr::If(BlockType::Void),
            Instr::I32Const(0),
            Instr::Return,
            Instr::End,
            Instr::LocalGet(3),
            Instr::I32Const(1),
            Instr::I32Add,
            Instr::LocalSet(3),
            Instr::Br(0),
            Instr::End,
            Instr::End,
            Instr::I32Const(1),
        ]);

        self.defined[def_slot].body = b;
        Ok(idx)
    }

    fn ensure_list_contains_fn(&mut self, elem_ty: &Type) -> Result<u32, String> {
        if let Some(&idx) = self.list_contains_fns.get(elem_ty) {
            return Ok(idx);
        }
        let idx = self.next_func_idx();
        let def_slot = self.defined.len();
        self.list_contains_fns.insert(elem_ty.clone(), idx);
        let elem_vt = self.slot_val_type(elem_ty)?;
        self.defined.push(DefinedFunc {
            name: format!("list_contains_{}", mangle_type(elem_ty)),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I32, elem_vt],
                results: vec![ValType::I32],
            },
            // locals: 0=list, 1=needle, 2=data(i32), 3=len(i32), 4=i(i32)
            extra_locals: vec![ValType::I32, ValType::I32, ValType::I32],
            body: Vec::new(),
        });

        let mut b = vec![
            Instr::LocalGet(0),
            Instr::I32Load(0),
            Instr::LocalSet(2),
            Instr::LocalGet(0),
            Instr::I32Load(4),
            Instr::LocalSet(3),
            Instr::I32Const(0),
            Instr::LocalSet(4),
            Instr::Block(BlockType::Void),
            Instr::Loop(BlockType::Void),
            Instr::LocalGet(4),
            Instr::LocalGet(3),
            Instr::I32GeS,
            Instr::BrIf(1),
            Instr::LocalGet(2),
            Instr::LocalGet(4),
            Instr::I32Const(3),
            Instr::I32Shl,
            Instr::I32Add,
            load_slot_instr(elem_vt, 0),
            Instr::LocalGet(1),
        ];
        self.emit_val_eq_instrs(elem_ty, &mut b)?;
        b.extend([
            Instr::If(BlockType::Void),
            Instr::I32Const(1),
            Instr::Return,
            Instr::End,
            Instr::LocalGet(4),
            Instr::I32Const(1),
            Instr::I32Add,
            Instr::LocalSet(4),
            Instr::Br(0),
            Instr::End,
            Instr::End,
            Instr::I32Const(0),
        ]);

        self.defined[def_slot].body = b;
        Ok(idx)
    }

    fn emit_val_eq_instrs(&mut self, ty: &Type, out: &mut Vec<Instr>) -> Result<(), String> {
        match ty {
            Type::Int => out.push(Instr::I64Eq),
            Type::Float => out.push(Instr::F64Eq),
            Type::Bool => out.push(Instr::I32Eq),
            Type::Str => out.push(Instr::Call(FN_STR_EQ)),
            Type::List(inner) => {
                let fidx = self.ensure_list_eq_fn(inner)?;
                out.push(Instr::Call(fidx));
            }
            Type::Named(n) => {
                if self.enums.contains_key(n) {
                    out.push(Instr::I64Eq);
                } else if let Some(&fidx) = self.struct_eq_fns.get(n) {
                    out.push(Instr::Call(fidx));
                } else {
                    return Err(format!("unknown type '{}' in equality comparison", n));
                }
            }
            Type::Void => return Err("cannot compare Void values".to_string()),
        }
        Ok(())
    }

    fn build_struct_eq_body(&mut self, s: &StructDecl) -> Result<Vec<Instr>, String> {
        let mut b = vec![
            Instr::LocalGet(0),
            Instr::LocalGet(1),
            Instr::I32Eq,
            Instr::If(BlockType::Void),
            Instr::I32Const(1),
            Instr::Return,
            Instr::End,
        ];
        for (fidx, field) in s.fields.iter().enumerate() {
            let offset = (fidx * 8) as u32;
            let fvt = self.slot_val_type(&field.ty)?;
            b.push(Instr::LocalGet(0));
            b.push(load_slot_instr(fvt, offset));
            b.push(Instr::LocalGet(1));
            b.push(load_slot_instr(fvt, offset));
            self.emit_val_eq_instrs(&field.ty, &mut b)?;
            b.extend([
                Instr::I32Eqz,
                Instr::If(BlockType::Void),
                Instr::I32Const(0),
                Instr::Return,
                Instr::End,
            ]);
        }
        b.push(Instr::I32Const(1));
        Ok(b)
    }

    fn emit_runtime_functions(&mut self) {
        // 7: $alloc(size: i32) -> i32
        self.defined.push(DefinedFunc {
            name: "alloc".to_string(),
            export_name: Some("__star_alloc".to_string()),
            sig: FuncSig {
                params: vec![ValType::I32],
                results: vec![ValType::I32],
            },
            extra_locals: vec![ValType::I32, ValType::I32, ValType::I32],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32Const(8),
                Instr::LocalGet(0),
                Instr::I32Const(0),
                Instr::I32GtS,
                Instr::Select,
                Instr::I32Const(7),
                Instr::I32Add,
                Instr::I32Const(-8),
                Instr::I32And,
                Instr::LocalSet(1),
                Instr::GlobalGet(0),
                Instr::LocalSet(2),
                Instr::LocalGet(2),
                Instr::LocalGet(1),
                Instr::I32Add,
                Instr::LocalSet(3),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(3),
                Instr::MemorySize,
                Instr::I32Const(16),
                Instr::I32Shl,
                Instr::I32LeU,
                Instr::BrIf(1),
                Instr::I32Const(4),
                Instr::MemoryGrow,
                Instr::I32Const(-1),
                Instr::I32Eq,
                Instr::If(BlockType::Void),
                Instr::Unreachable,
                Instr::End,
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::LocalGet(3),
                Instr::GlobalSet(0),
                Instr::LocalGet(2),
            ],
        });

        // 8: $i64_min
        self.defined.push(DefinedFunc {
            name: "i64_min".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64, ValType::I64],
                results: vec![ValType::I64],
            },
            extra_locals: vec![],
            body: vec![
                Instr::LocalGet(0),
                Instr::LocalGet(1),
                Instr::LocalGet(0),
                Instr::LocalGet(1),
                Instr::I64LtS,
                Instr::Select,
            ],
        });

        // 9: $i64_max
        self.defined.push(DefinedFunc {
            name: "i64_max".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64, ValType::I64],
                results: vec![ValType::I64],
            },
            extra_locals: vec![],
            body: vec![
                Instr::LocalGet(0),
                Instr::LocalGet(1),
                Instr::LocalGet(0),
                Instr::LocalGet(1),
                Instr::I64GtS,
                Instr::Select,
            ],
        });

        // 10: $i64_abs
        self.defined.push(DefinedFunc {
            name: "i64_abs".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64],
                results: vec![ValType::I64],
            },
            extra_locals: vec![],
            body: vec![
                Instr::I64Const(0),
                Instr::LocalGet(0),
                Instr::I64Sub,
                Instr::LocalGet(0),
                Instr::LocalGet(0),
                Instr::I64Const(0),
                Instr::I64LtS,
                Instr::Select,
            ],
        });

        // 11: $str_eq(a: i64, b: i64) -> i32
        self.defined.push(DefinedFunc {
            name: "str_eq".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64, ValType::I64],
                results: vec![ValType::I32],
            },
            extra_locals: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            body: vec![
                Instr::LocalGet(0),
                Instr::LocalGet(1),
                Instr::I64Eq,
                Instr::If(BlockType::Void),
                Instr::I32Const(1),
                Instr::Return,
                Instr::End,
                Instr::LocalGet(0),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::LocalSet(2),
                Instr::LocalGet(2),
                Instr::LocalGet(1),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::I32Ne,
                Instr::If(BlockType::Void),
                Instr::I32Const(0),
                Instr::Return,
                Instr::End,
                Instr::LocalGet(0),
                Instr::I32WrapI64,
                Instr::LocalSet(3),
                Instr::LocalGet(1),
                Instr::I32WrapI64,
                Instr::LocalSet(4),
                Instr::I32Const(0),
                Instr::LocalSet(5),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(5),
                Instr::LocalGet(2),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(3),
                Instr::LocalGet(5),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::LocalGet(4),
                Instr::LocalGet(5),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::I32Ne,
                Instr::If(BlockType::Void),
                Instr::I32Const(0),
                Instr::Return,
                Instr::End,
                Instr::LocalGet(5),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(5),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::I32Const(1),
            ],
        });

        // 12: $str_concat(a: i64, b: i64) -> i64
        // locals: 0=a, 1=b, 2=ptr_a, 3=len_a, 4=ptr_b, 5=len_b, 6=dst, 7=i
        self.defined.push(DefinedFunc {
            name: "str_concat".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64, ValType::I64],
                results: vec![ValType::I64],
            },
            extra_locals: vec![
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
            ],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32WrapI64,
                Instr::LocalSet(2),
                Instr::LocalGet(0),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::LocalSet(3),
                Instr::LocalGet(1),
                Instr::I32WrapI64,
                Instr::LocalSet(4),
                Instr::LocalGet(1),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::LocalSet(5),
                Instr::LocalGet(3),
                Instr::LocalGet(5),
                Instr::I32Add,
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(6),
                // copy a
                Instr::I32Const(0),
                Instr::LocalSet(7),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(7),
                Instr::LocalGet(3),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(6),
                Instr::LocalGet(7),
                Instr::I32Add,
                Instr::LocalGet(2),
                Instr::LocalGet(7),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::I32Store8(0),
                Instr::LocalGet(7),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(7),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                // copy b
                Instr::I32Const(0),
                Instr::LocalSet(7),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(7),
                Instr::LocalGet(5),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(6),
                Instr::LocalGet(3),
                Instr::I32Add,
                Instr::LocalGet(7),
                Instr::I32Add,
                Instr::LocalGet(4),
                Instr::LocalGet(7),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::I32Store8(0),
                Instr::LocalGet(7),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(7),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                // pack (dst | ((len_a + len_b) << 32))
                Instr::LocalGet(6),
                Instr::I64ExtendI32U,
                Instr::LocalGet(3),
                Instr::LocalGet(5),
                Instr::I32Add,
                Instr::I64ExtendI32U,
                Instr::I64Const(32),
                Instr::I64Shl,
                Instr::I64Or,
            ],
        });

        // 13: $str_contains(h: i64, n: i64) -> i32
        // locals: 0=h, 1=n, 2=ptr_h, 3=len_h, 4=ptr_n, 5=len_n, 6=pos, 7=k, 8=ok
        self.defined.push(DefinedFunc {
            name: "str_contains".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64, ValType::I64],
                results: vec![ValType::I32],
            },
            extra_locals: vec![
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
            ],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32WrapI64,
                Instr::LocalSet(2),
                Instr::LocalGet(0),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::LocalSet(3),
                Instr::LocalGet(1),
                Instr::I32WrapI64,
                Instr::LocalSet(4),
                Instr::LocalGet(1),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::LocalSet(5),
                Instr::LocalGet(5),
                Instr::I32Eqz,
                Instr::If(BlockType::Void),
                Instr::I32Const(1),
                Instr::Return,
                Instr::End,
                Instr::LocalGet(5),
                Instr::LocalGet(3),
                Instr::I32GtS,
                Instr::If(BlockType::Void),
                Instr::I32Const(0),
                Instr::Return,
                Instr::End,
                Instr::I32Const(0),
                Instr::LocalSet(6),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(6),
                Instr::LocalGet(3),
                Instr::LocalGet(5),
                Instr::I32Sub,
                Instr::I32GtS,
                Instr::BrIf(1),
                Instr::I32Const(1),
                Instr::LocalSet(8),
                Instr::I32Const(0),
                Instr::LocalSet(7),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(7),
                Instr::LocalGet(5),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(2),
                Instr::LocalGet(6),
                Instr::I32Add,
                Instr::LocalGet(7),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::LocalGet(4),
                Instr::LocalGet(7),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::I32Ne,
                Instr::If(BlockType::Void),
                Instr::I32Const(0),
                Instr::LocalSet(8),
                Instr::Br(2),
                Instr::End,
                Instr::LocalGet(7),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(7),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::LocalGet(8),
                Instr::If(BlockType::Void),
                Instr::I32Const(1),
                Instr::Return,
                Instr::End,
                Instr::LocalGet(6),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(6),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::I32Const(0),
            ],
        });

        // 14: $str_upper(s: i64) -> i64
        self.defined
            .push(self.build_case_map_fn("str_upper", 97, 122, -32));
        // 15: $str_lower(s: i64) -> i64
        self.defined
            .push(self.build_case_map_fn("str_lower", 65, 90, 32));

        // 16: $i64_to_str(v: i64) -> i64
        // locals: 0=v, 1=neg(i32), 2=mag(i64), 3=tmp(i32), 4=n(i32), 5=dst(i32), 6=i(i32)
        self.defined.push(DefinedFunc {
            name: "i64_to_str".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64],
                results: vec![ValType::I64],
            },
            extra_locals: vec![
                ValType::I32,
                ValType::I64,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
            ],
            body: vec![
                Instr::LocalGet(0),
                Instr::I64Eqz,
                Instr::If(BlockType::Void),
                Instr::I32Const(1),
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(5),
                Instr::LocalGet(5),
                Instr::I32Const(48),
                Instr::I32Store8(0),
                Instr::LocalGet(5),
                Instr::I64ExtendI32U,
                Instr::I64Const(1_i64 << 32),
                Instr::I64Or,
                Instr::Return,
                Instr::End,
                Instr::LocalGet(0),
                Instr::I64Const(0),
                Instr::I64LtS,
                Instr::If(BlockType::Void),
                Instr::I32Const(1),
                Instr::LocalSet(1),
                Instr::I64Const(0),
                Instr::LocalGet(0),
                Instr::I64Sub,
                Instr::LocalSet(2),
                Instr::Else,
                Instr::I32Const(0),
                Instr::LocalSet(1),
                Instr::LocalGet(0),
                Instr::LocalSet(2),
                Instr::End,
                Instr::I32Const(24),
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(3),
                Instr::I32Const(0),
                Instr::LocalSet(4),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(2),
                Instr::I64Eqz,
                Instr::BrIf(1),
                Instr::LocalGet(3),
                Instr::LocalGet(4),
                Instr::I32Add,
                Instr::LocalGet(2),
                Instr::I64Const(10),
                Instr::I64RemU,
                Instr::I32WrapI64,
                Instr::I32Const(48),
                Instr::I32Add,
                Instr::I32Store8(0),
                Instr::LocalGet(2),
                Instr::I64Const(10),
                Instr::I64DivU,
                Instr::LocalSet(2),
                Instr::LocalGet(4),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(4),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::LocalGet(1),
                Instr::If(BlockType::Void),
                Instr::LocalGet(3),
                Instr::LocalGet(4),
                Instr::I32Add,
                Instr::I32Const(45),
                Instr::I32Store8(0),
                Instr::LocalGet(4),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(4),
                Instr::End,
                Instr::LocalGet(4),
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(5),
                Instr::I32Const(0),
                Instr::LocalSet(6),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(6),
                Instr::LocalGet(4),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(5),
                Instr::LocalGet(6),
                Instr::I32Add,
                Instr::LocalGet(3),
                Instr::LocalGet(4),
                Instr::I32Const(1),
                Instr::I32Sub,
                Instr::LocalGet(6),
                Instr::I32Sub,
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::I32Store8(0),
                Instr::LocalGet(6),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(6),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::LocalGet(5),
                Instr::I64ExtendI32U,
                Instr::LocalGet(4),
                Instr::I64ExtendI32U,
                Instr::I64Const(32),
                Instr::I64Shl,
                Instr::I64Or,
            ],
        });

        // 17: $bool_to_str(b: i32) -> i64
        self.defined.push(DefinedFunc {
            name: "bool_to_str".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I32],
                results: vec![ValType::I64],
            },
            extra_locals: vec![],
            body: vec![
                Instr::I64Const(self.packed_true),
                Instr::I64Const(self.packed_false),
                Instr::LocalGet(0),
                Instr::Select,
            ],
        });

        // 18: $list_new(init_cap: i32) -> i32
        self.defined.push(DefinedFunc {
            name: "list_new".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I32],
                results: vec![ValType::I32],
            },
            extra_locals: vec![ValType::I32, ValType::I32, ValType::I32],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32Const(4),
                Instr::LocalGet(0),
                Instr::I32Const(4),
                Instr::I32GtS,
                Instr::Select,
                Instr::LocalSet(1),
                Instr::I32Const(16),
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(2),
                Instr::LocalGet(1),
                Instr::I32Const(3),
                Instr::I32Shl,
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(3),
                Instr::LocalGet(2),
                Instr::LocalGet(3),
                Instr::I32Store(0),
                Instr::LocalGet(2),
                Instr::I32Const(0),
                Instr::I32Store(4),
                Instr::LocalGet(2),
                Instr::LocalGet(1),
                Instr::I32Store(8),
                Instr::LocalGet(2),
            ],
        });

        // 19: $list_ensure_push_slot(hdr: i32) -> i32
        self.defined.push(DefinedFunc {
            name: "list_ensure_push_slot".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I32],
                results: vec![ValType::I32],
            },
            extra_locals: vec![
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
            ],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32Load(0),
                Instr::LocalSet(1),
                Instr::LocalGet(0),
                Instr::I32Load(4),
                Instr::LocalSet(2),
                Instr::LocalGet(0),
                Instr::I32Load(8),
                Instr::LocalSet(3),
                Instr::LocalGet(2),
                Instr::LocalGet(3),
                Instr::I32GeS,
                Instr::If(BlockType::Void),
                Instr::LocalGet(3),
                Instr::I32Const(1),
                Instr::I32Shl,
                Instr::LocalSet(4),
                Instr::LocalGet(4),
                Instr::I32Const(3),
                Instr::I32Shl,
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(5),
                Instr::I32Const(0),
                Instr::LocalSet(6),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(6),
                Instr::LocalGet(2),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(5),
                Instr::LocalGet(6),
                Instr::I32Const(3),
                Instr::I32Shl,
                Instr::I32Add,
                Instr::LocalGet(1),
                Instr::LocalGet(6),
                Instr::I32Const(3),
                Instr::I32Shl,
                Instr::I32Add,
                Instr::I64Load(0),
                Instr::I64Store(0),
                Instr::LocalGet(6),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(6),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::LocalGet(0),
                Instr::LocalGet(5),
                Instr::I32Store(0),
                Instr::LocalGet(0),
                Instr::LocalGet(4),
                Instr::I32Store(8),
                Instr::LocalGet(5),
                Instr::LocalSet(1),
                Instr::End,
                Instr::LocalGet(0),
                Instr::LocalGet(2),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::I32Store(4),
                Instr::LocalGet(1),
                Instr::LocalGet(2),
                Instr::I32Const(3),
                Instr::I32Shl,
                Instr::I32Add,
            ],
        });

        // 20: $list_slot_addr(hdr: i32, idx: i64) -> i32
        self.defined.push(DefinedFunc {
            name: "list_slot_addr".to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I32, ValType::I64],
                results: vec![ValType::I32],
            },
            extra_locals: vec![ValType::I32],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32Load(4),
                Instr::LocalSet(2),
                Instr::LocalGet(1),
                Instr::I64Const(0),
                Instr::I64LtS,
                Instr::If(BlockType::Void),
                Instr::Unreachable,
                Instr::End,
                Instr::LocalGet(1),
                Instr::LocalGet(2),
                Instr::I64ExtendI32S,
                Instr::I64GeS,
                Instr::If(BlockType::Void),
                Instr::Unreachable,
                Instr::End,
                Instr::LocalGet(0),
                Instr::I32Load(0),
                Instr::LocalGet(1),
                Instr::I32WrapI64,
                Instr::I32Const(3),
                Instr::I32Shl,
                Instr::I32Add,
            ],
        });
    }

    fn build_case_map_fn(&self, name: &str, lo: i32, hi: i32, delta: i32) -> DefinedFunc {
        // locals: 0=s(i64), 1=ptr(i32), 2=len(i32), 3=dst(i32), 4=i(i32), 5=ch(i32)
        DefinedFunc {
            name: name.to_string(),
            export_name: None,
            sig: FuncSig {
                params: vec![ValType::I64],
                results: vec![ValType::I64],
            },
            extra_locals: vec![
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
                ValType::I32,
            ],
            body: vec![
                Instr::LocalGet(0),
                Instr::I32WrapI64,
                Instr::LocalSet(1),
                Instr::LocalGet(0),
                Instr::I64Const(32),
                Instr::I64ShrU,
                Instr::I32WrapI64,
                Instr::LocalSet(2),
                Instr::LocalGet(2),
                Instr::Call(FN_ALLOC),
                Instr::LocalSet(3),
                Instr::I32Const(0),
                Instr::LocalSet(4),
                Instr::Block(BlockType::Void),
                Instr::Loop(BlockType::Void),
                Instr::LocalGet(4),
                Instr::LocalGet(2),
                Instr::I32GeS,
                Instr::BrIf(1),
                Instr::LocalGet(1),
                Instr::LocalGet(4),
                Instr::I32Add,
                Instr::I32Load8U(0),
                Instr::LocalSet(5),
                Instr::LocalGet(5),
                Instr::I32Const(lo),
                Instr::I32GeS,
                Instr::LocalGet(5),
                Instr::I32Const(hi),
                Instr::I32LeS,
                Instr::I32And,
                Instr::If(BlockType::Void),
                Instr::LocalGet(5),
                Instr::I32Const(delta),
                Instr::I32Add,
                Instr::LocalSet(5),
                Instr::End,
                Instr::LocalGet(3),
                Instr::LocalGet(4),
                Instr::I32Add,
                Instr::LocalGet(5),
                Instr::I32Store8(0),
                Instr::LocalGet(4),
                Instr::I32Const(1),
                Instr::I32Add,
                Instr::LocalSet(4),
                Instr::Br(0),
                Instr::End,
                Instr::End,
                Instr::LocalGet(3),
                Instr::I64ExtendI32U,
                Instr::LocalGet(2),
                Instr::I64ExtendI32U,
                Instr::I64Const(32),
                Instr::I64Shl,
                Instr::I64Or,
            ],
        }
    }

    fn compile_fn_body(&mut self, f: &'a FnDecl) -> Result<(Vec<ValType>, Vec<Instr>), String> {
        let mut ctx = FnCodegen::new(f.params.len() as u32, f.ret_ty.clone());
        let mut root_scope = HashMap::new();
        for (idx, p) in f.params.iter().enumerate() {
            root_scope.insert(p.name.clone(), (idx as u32, p.ty.clone()));
        }
        ctx.scopes.push(root_scope);
        ctx.collect_list_hints(&f.body, self.hub);
        self.emit_stmts(&f.body, &mut ctx)?;
        if f.ret_ty != Type::Void {
            ctx.body.push(Instr::Unreachable);
        }
        Ok((ctx.extra_locals, ctx.body))
    }

    fn compile_test_body(&mut self, t: &'a TestDecl) -> Result<(Vec<ValType>, Vec<Instr>), String> {
        let mut ctx = FnCodegen::new(0, Type::Void);
        ctx.scopes.push(HashMap::new());
        ctx.collect_list_hints(&t.body, self.hub);
        self.emit_stmts(&t.body, &mut ctx)?;
        Ok((ctx.extra_locals, ctx.body))
    }

    fn emit_stmts(&mut self, stmts: &[Stmt], ctx: &mut FnCodegen) -> Result<(), String> {
        for s in stmts {
            self.emit_stmt(s, ctx)?;
        }
        Ok(())
    }

    fn emit_stmt(&mut self, stmt: &Stmt, ctx: &mut FnCodegen) -> Result<(), String> {
        match stmt {
            Stmt::Comment { .. } => {}
            Stmt::Let {
                name, ty, value, ..
            } => {
                let resolved_ty = ty
                    .clone()
                    .or_else(|| ctx.infer_type(value, self.hub))
                    .or_else(|| ctx.list_hints.get(name).cloned())
                    .ok_or_else(|| format!("cannot infer Wasm type for local '{}'", name))?;
                let vt = self.slot_val_type(&resolved_ty)?;
                let lidx = ctx.alloc_local(vt);
                self.emit_expr(value, Some(&resolved_ty), ctx)?;
                ctx.body.push(Instr::LocalSet(lidx));
                ctx.define_var(name.clone(), lidx, resolved_ty);
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                match target {
                    AssignTarget::Var(v) => {
                        let (lidx, vty) = ctx
                            .lookup_var(v)
                            .ok_or_else(|| format!("unknown variable '{}'", v))?;
                        match op {
                            AssignOp::Set => {
                                self.emit_expr(value, Some(&vty), ctx)?;
                                ctx.body.push(Instr::LocalSet(lidx));
                            }
                            AssignOp::AddAssign | AssignOp::SubAssign => {
                                ctx.body.push(Instr::LocalGet(lidx));
                                self.emit_expr(value, Some(&vty), ctx)?;
                                self.emit_compound_op(*op, &vty, &mut ctx.body)?;
                                ctx.body.push(Instr::LocalSet(lidx));
                            }
                        }
                    }
                    AssignTarget::Field { base, field } => {
                        let (b_idx, b_ty) = ctx
                            .lookup_var(base)
                            .ok_or_else(|| format!("unknown struct variable '{}'", base))?;
                        let Type::Named(sname) = b_ty else {
                            return Err(format!("'{}' is not a struct", base));
                        };
                        let sdecl = self
                            .structs
                            .get(&sname)
                            .copied()
                            .ok_or_else(|| format!("unknown struct '{}'", sname))?;
                        let (fpos, fdecl) = sdecl
                            .fields
                            .iter()
                            .enumerate()
                            .find(|(_, f)| &f.name == field)
                            .ok_or_else(|| format!("unknown field '{}.{}'", sname, field))?;
                        let offset = (fpos * 8) as u32;
                        let fvt = self.slot_val_type(&fdecl.ty)?;
                        ctx.body.push(Instr::LocalGet(b_idx));
                        match op {
                            AssignOp::Set => {
                                self.emit_expr(value, Some(&fdecl.ty), ctx)?;
                            }
                            AssignOp::AddAssign | AssignOp::SubAssign => {
                                ctx.body.push(Instr::LocalGet(b_idx));
                                ctx.body.push(load_slot_instr(fvt, offset));
                                self.emit_expr(value, Some(&fdecl.ty), ctx)?;
                                self.emit_compound_op(*op, &fdecl.ty, &mut ctx.body)?;
                            }
                        }
                        ctx.body.push(store_slot_instr(fvt, offset));
                    }
                    AssignTarget::Index { base, index } => {
                        let (b_idx, b_ty) = ctx
                            .lookup_var(base)
                            .ok_or_else(|| format!("unknown list variable '{}'", base))?;
                        let Type::List(elem_ty) = b_ty else {
                            return Err(format!("'{}' is not a list", base));
                        };
                        let elem_vt = self.slot_val_type(&elem_ty)?;
                        let addr_local = ctx.alloc_local(ValType::I32);
                        ctx.body.push(Instr::LocalGet(b_idx));
                        self.emit_expr(index, Some(&Type::Int), ctx)?;
                        ctx.body.push(Instr::Call(FN_LIST_SLOT_ADDR));
                        ctx.body.push(Instr::LocalSet(addr_local));

                        ctx.body.push(Instr::LocalGet(addr_local));
                        match op {
                            AssignOp::Set => {
                                self.emit_expr(value, Some(&elem_ty), ctx)?;
                            }
                            AssignOp::AddAssign | AssignOp::SubAssign => {
                                ctx.body.push(Instr::LocalGet(addr_local));
                                ctx.body.push(load_slot_instr(elem_vt, 0));
                                self.emit_expr(value, Some(&elem_ty), ctx)?;
                                self.emit_compound_op(*op, &elem_ty, &mut ctx.body)?;
                            }
                        }
                        ctx.body.push(store_slot_instr(elem_vt, 0));
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.emit_expr(cond, Some(&Type::Bool), ctx)?;
                ctx.body.push(Instr::If(BlockType::Void));
                ctx.ctrl.push(CtrlKind::Plain);

                ctx.scopes.push(HashMap::new());
                self.emit_stmts(then_body, ctx)?;
                ctx.scopes.pop();

                if !else_body.is_empty() {
                    ctx.body.push(Instr::Else);
                    ctx.scopes.push(HashMap::new());
                    self.emit_stmts(else_body, ctx)?;
                    ctx.scopes.pop();
                }

                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
            }
            Stmt::Match { expr, arms, .. } => {
                let scrut_ty = ctx
                    .infer_type(expr, self.hub)
                    .ok_or_else(|| "cannot infer match scrutinee type".to_string())?;
                let scrut_vt = self.slot_val_type(&scrut_ty)?;
                let scrut_local = ctx.alloc_local(scrut_vt);
                self.emit_expr(expr, Some(&scrut_ty), ctx)?;
                ctx.body.push(Instr::LocalSet(scrut_local));
                self.emit_match_arms(scrut_local, &scrut_ty, arms, ctx)?;
            }
            Stmt::While { cond, body, .. } => {
                ctx.body.push(Instr::Block(BlockType::Void));
                ctx.ctrl.push(CtrlKind::LoopBreak);
                ctx.body.push(Instr::Loop(BlockType::Void));
                ctx.ctrl.push(CtrlKind::Plain);

                self.emit_expr(cond, Some(&Type::Bool), ctx)?;
                ctx.body.push(Instr::I32Eqz);
                ctx.body.push(Instr::BrIf(1));

                ctx.body.push(Instr::Block(BlockType::Void));
                ctx.ctrl.push(CtrlKind::LoopContinue);
                ctx.scopes.push(HashMap::new());
                self.emit_stmts(body, ctx)?;
                ctx.scopes.pop();
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);

                ctx.body.push(Instr::Br(0));
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let var_local = ctx.alloc_local(ValType::I64);
                let end_local = ctx.alloc_local(ValType::I64);
                self.emit_expr(start, Some(&Type::Int), ctx)?;
                ctx.body.push(Instr::LocalSet(var_local));
                self.emit_expr(end, Some(&Type::Int), ctx)?;
                ctx.body.push(Instr::LocalSet(end_local));

                ctx.body.push(Instr::Block(BlockType::Void));
                ctx.ctrl.push(CtrlKind::LoopBreak);
                ctx.body.push(Instr::Loop(BlockType::Void));
                ctx.ctrl.push(CtrlKind::Plain);

                ctx.body.push(Instr::LocalGet(var_local));
                ctx.body.push(Instr::LocalGet(end_local));
                ctx.body.push(Instr::I64GeS);
                ctx.body.push(Instr::BrIf(1));

                ctx.body.push(Instr::Block(BlockType::Void));
                ctx.ctrl.push(CtrlKind::LoopContinue);
                let mut loop_scope = HashMap::new();
                loop_scope.insert(var.clone(), (var_local, Type::Int));
                ctx.scopes.push(loop_scope);
                self.emit_stmts(body, ctx)?;
                ctx.scopes.pop();
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);

                // Step increment: var += 1
                ctx.body.push(Instr::LocalGet(var_local));
                ctx.body.push(Instr::I64Const(1));
                ctx.body.push(Instr::I64Add);
                ctx.body.push(Instr::LocalSet(var_local));

                ctx.body.push(Instr::Br(0));
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let iter_ty = ctx
                    .infer_type(iter, self.hub)
                    .ok_or_else(|| "cannot infer ForEach list type".to_string())?;
                let Type::List(elem_ty) = iter_ty else {
                    return Err("ForEach target is not a List".to_string());
                };
                let elem_vt = self.slot_val_type(&elem_ty)?;
                let list_local = ctx.alloc_local(ValType::I32);
                let idx_local = ctx.alloc_local(ValType::I32);
                let var_local = ctx.alloc_local(elem_vt);

                self.emit_expr(iter, Some(&Type::List(elem_ty.clone())), ctx)?;
                ctx.body.push(Instr::LocalSet(list_local));
                ctx.body.push(Instr::I32Const(0));
                ctx.body.push(Instr::LocalSet(idx_local));

                ctx.body.push(Instr::Block(BlockType::Void));
                ctx.ctrl.push(CtrlKind::LoopBreak);
                ctx.body.push(Instr::Loop(BlockType::Void));
                ctx.ctrl.push(CtrlKind::Plain);

                ctx.body.push(Instr::LocalGet(idx_local));
                ctx.body.push(Instr::LocalGet(list_local));
                ctx.body.push(Instr::I32Load(4));
                ctx.body.push(Instr::I32GeS);
                ctx.body.push(Instr::BrIf(1));

                // var = load(load_i32(list_local) + idx_local * 8)
                ctx.body.push(Instr::LocalGet(list_local));
                ctx.body.push(Instr::I32Load(0));
                ctx.body.push(Instr::LocalGet(idx_local));
                ctx.body.push(Instr::I32Const(3));
                ctx.body.push(Instr::I32Shl);
                ctx.body.push(Instr::I32Add);
                ctx.body.push(load_slot_instr(elem_vt, 0));
                ctx.body.push(Instr::LocalSet(var_local));

                ctx.body.push(Instr::Block(BlockType::Void));
                ctx.ctrl.push(CtrlKind::LoopContinue);
                let mut loop_scope = HashMap::new();
                loop_scope.insert(var.clone(), (var_local, *elem_ty));
                ctx.scopes.push(loop_scope);
                self.emit_stmts(body, ctx)?;
                ctx.scopes.pop();
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);

                ctx.body.push(Instr::LocalGet(idx_local));
                ctx.body.push(Instr::I32Const(1));
                ctx.body.push(Instr::I32Add);
                ctx.body.push(Instr::LocalSet(idx_local));

                ctx.body.push(Instr::Br(0));
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
                ctx.ctrl.pop();
                ctx.body.push(Instr::End);
            }
            Stmt::Break { .. } => {
                let depth = ctx
                    .branch_depth(CtrlKind::LoopBreak)
                    .ok_or_else(|| "break outside loop".to_string())?;
                ctx.body.push(Instr::Br(depth));
            }
            Stmt::Continue { .. } => {
                let depth = ctx
                    .branch_depth(CtrlKind::LoopContinue)
                    .ok_or_else(|| "continue outside loop".to_string())?;
                ctx.body.push(Instr::Br(depth));
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    let expected = ctx.ret_ty.clone();
                    self.emit_expr(v, Some(&expected), ctx)?;
                }
                ctx.body.push(Instr::Return);
            }
            Stmt::Assert { cond, .. } => {
                self.emit_expr(cond, Some(&Type::Bool), ctx)?;
                ctx.body.push(Instr::I32Eqz);
                ctx.body.push(Instr::If(BlockType::Void));
                ctx.body.push(Instr::Unreachable);
                ctx.body.push(Instr::End);
            }
            Stmt::AssertEq { left, right, .. } => {
                let lty = ctx
                    .infer_type(left, self.hub)
                    .or_else(|| ctx.infer_type(right, self.hub))
                    .ok_or_else(|| "cannot infer AssertEq operand type".to_string())?;
                self.emit_expr(left, Some(&lty), ctx)?;
                self.emit_expr(right, Some(&lty), ctx)?;
                self.emit_val_eq_instrs(&lty, &mut ctx.body)?;
                ctx.body.push(Instr::I32Eqz);
                ctx.body.push(Instr::If(BlockType::Void));
                ctx.body.push(Instr::Unreachable);
                ctx.body.push(Instr::End);
            }
            Stmt::Expr { expr, .. } => {
                let ety = ctx.infer_type(expr, self.hub).unwrap_or(Type::Void);
                self.emit_expr(expr, Some(&ety), ctx)?;
                if self.val_type_of(&ety)?.is_some() {
                    ctx.body.push(Instr::Drop);
                }
            }
        }
        Ok(())
    }

    #[allow(clippy::only_used_in_recursion)]
    fn emit_match_arms(
        &mut self,
        scrut_local: u32,
        scrut_ty: &Type,
        arms: &[MatchArm],
        ctx: &mut FnCodegen,
    ) -> Result<(), String> {
        let Some((first, rest)) = arms.split_first() else {
            return Ok(());
        };
        if first.pat == MatchPat::Wildcard {
            ctx.scopes.push(HashMap::new());
            self.emit_stmts(&first.body, ctx)?;
            ctx.scopes.pop();
            return Ok(());
        }

        ctx.body.push(Instr::LocalGet(scrut_local));
        match &first.pat {
            MatchPat::Int(v) => {
                ctx.body.push(Instr::I64Const(*v));
                ctx.body.push(Instr::I64Eq);
            }
            MatchPat::Str(s) => {
                let packed = self.intern_str(s);
                ctx.body.push(Instr::I64Const(packed));
                ctx.body.push(Instr::Call(FN_STR_EQ));
            }
            MatchPat::EnumVariant { enum_name, variant } => {
                let disc = self
                    .enums
                    .get(enum_name)
                    .and_then(|m| m.get(variant))
                    .copied()
                    .ok_or_else(|| format!("unknown enum variant '{}::{}'", enum_name, variant))?;
                ctx.body.push(Instr::I64Const(disc));
                ctx.body.push(Instr::I64Eq);
            }
            MatchPat::Wildcard => unreachable!(),
        }

        ctx.body.push(Instr::If(BlockType::Void));
        ctx.ctrl.push(CtrlKind::Plain);
        ctx.scopes.push(HashMap::new());
        self.emit_stmts(&first.body, ctx)?;
        ctx.scopes.pop();

        if !rest.is_empty() {
            ctx.body.push(Instr::Else);
            self.emit_match_arms(scrut_local, scrut_ty, rest, ctx)?;
        }

        ctx.ctrl.pop();
        ctx.body.push(Instr::End);
        Ok(())
    }

    fn emit_compound_op(
        &self,
        op: AssignOp,
        ty: &Type,
        out: &mut Vec<Instr>,
    ) -> Result<(), String> {
        match (op, ty) {
            (AssignOp::AddAssign, Type::Int) => out.push(Instr::I64Add),
            (AssignOp::SubAssign, Type::Int) => out.push(Instr::I64Sub),
            (AssignOp::AddAssign, Type::Float) => out.push(Instr::F64Add),
            (AssignOp::SubAssign, Type::Float) => out.push(Instr::F64Sub),
            (AssignOp::AddAssign, Type::Str) => out.push(Instr::Call(FN_STR_CONCAT)),
            _ => return Err(format!("unsupported compound assignment on {:?}", ty)),
        }
        Ok(())
    }

    fn emit_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
        ctx: &mut FnCodegen,
    ) -> Result<(), String> {
        match expr {
            Expr::Int(v) => ctx.body.push(Instr::I64Const(*v)),
            Expr::Float(v) => ctx.body.push(Instr::F64Const(*v)),
            Expr::Bool(b) => ctx.body.push(Instr::I32Const(if *b { 1 } else { 0 })),
            Expr::Str(s) => {
                let packed = self.intern_str(s);
                ctx.body.push(Instr::I64Const(packed));
            }
            Expr::Var(name) => {
                let (lidx, _) = ctx
                    .lookup_var(name)
                    .ok_or_else(|| format!("unknown variable '{}'", name))?;
                ctx.body.push(Instr::LocalGet(lidx));
            }
            Expr::EnumVariant { enum_name, variant } => {
                let disc = self
                    .enums
                    .get(enum_name)
                    .and_then(|m| m.get(variant))
                    .copied()
                    .ok_or_else(|| format!("unknown enum variant '{}::{}'", enum_name, variant))?;
                ctx.body.push(Instr::I64Const(disc));
            }
            Expr::List(items) => {
                let elem_ty = match expected {
                    Some(Type::List(inner)) => (**inner).clone(),
                    _ => {
                        if let Some(first) = items.first() {
                            ctx.infer_type(first, self.hub)
                                .ok_or_else(|| "cannot infer list element type".to_string())?
                        } else {
                            Type::Int
                        }
                    }
                };
                let elem_vt = self.slot_val_type(&elem_ty)?;
                let hdr_local = ctx.alloc_local(ValType::I32);
                let val_local = ctx.alloc_local(elem_vt);

                ctx.body.push(Instr::I32Const(items.len().max(4) as i32));
                ctx.body.push(Instr::Call(FN_LIST_NEW));
                ctx.body.push(Instr::LocalSet(hdr_local));

                for item in items {
                    self.emit_expr(item, Some(&elem_ty), ctx)?;
                    ctx.body.push(Instr::LocalSet(val_local));
                    ctx.body.push(Instr::LocalGet(hdr_local));
                    ctx.body.push(Instr::Call(FN_LIST_PUSH_SLOT));
                    ctx.body.push(Instr::LocalGet(val_local));
                    ctx.body.push(store_slot_instr(elem_vt, 0));
                }
                ctx.body.push(Instr::LocalGet(hdr_local));
            }
            Expr::StructInit { name, fields } => {
                let sdecl = self
                    .structs
                    .get(name)
                    .copied()
                    .ok_or_else(|| format!("unknown struct '{}'", name))?;
                let ptr_local = ctx.alloc_local(ValType::I32);
                let byte_size = (sdecl.fields.len().max(1) * 8) as i32;
                ctx.body.push(Instr::I32Const(byte_size));
                ctx.body.push(Instr::Call(FN_ALLOC));
                ctx.body.push(Instr::LocalSet(ptr_local));

                for (fpos, fdecl) in sdecl.fields.iter().enumerate() {
                    let (_, fexpr) = fields
                        .iter()
                        .find(|(fname, _)| fname == &fdecl.name)
                        .ok_or_else(|| {
                            format!("missing field '{}' in struct '{}'", fdecl.name, name)
                        })?;
                    let fvt = self.slot_val_type(&fdecl.ty)?;
                    ctx.body.push(Instr::LocalGet(ptr_local));
                    self.emit_expr(fexpr, Some(&fdecl.ty), ctx)?;
                    ctx.body.push(store_slot_instr(fvt, (fpos * 8) as u32));
                }
                ctx.body.push(Instr::LocalGet(ptr_local));
            }
            Expr::FieldAccess { base, field } => {
                let bty = ctx
                    .infer_type(base, self.hub)
                    .ok_or_else(|| "cannot infer struct base type".to_string())?;
                let Type::Named(sname) = bty else {
                    return Err("field access on non-struct type".to_string());
                };
                let sdecl = self
                    .structs
                    .get(&sname)
                    .copied()
                    .ok_or_else(|| format!("unknown struct '{}'", sname))?;
                let (fpos, fdecl) = sdecl
                    .fields
                    .iter()
                    .enumerate()
                    .find(|(_, f)| &f.name == field)
                    .ok_or_else(|| format!("unknown field '{}.{}'", sname, field))?;
                let fvt = self.slot_val_type(&fdecl.ty)?;
                self.emit_expr(base, Some(&Type::Named(sname)), ctx)?;
                ctx.body.push(load_slot_instr(fvt, (fpos * 8) as u32));
            }
            Expr::Index { base, index } => {
                let bty = ctx
                    .infer_type(base, self.hub)
                    .ok_or_else(|| "cannot infer indexed list type".to_string())?;
                let Type::List(elem_ty) = bty else {
                    return Err("indexing non-list type".to_string());
                };
                let elem_vt = self.slot_val_type(&elem_ty)?;
                self.emit_expr(base, Some(&Type::List(elem_ty)), ctx)?;
                self.emit_expr(index, Some(&Type::Int), ctx)?;
                ctx.body.push(Instr::Call(FN_LIST_SLOT_ADDR));
                ctx.body.push(load_slot_instr(elem_vt, 0));
            }
            Expr::Unary { op, expr: inner } => {
                let ity = ctx
                    .infer_type(inner, self.hub)
                    .or_else(|| expected.cloned())
                    .ok_or_else(|| "cannot infer unary operand type".to_string())?;
                match (op, &ity) {
                    (UnaryOp::Neg, Type::Int) => {
                        ctx.body.push(Instr::I64Const(0));
                        self.emit_expr(inner, Some(&Type::Int), ctx)?;
                        ctx.body.push(Instr::I64Sub);
                    }
                    (UnaryOp::Neg, Type::Float) => {
                        self.emit_expr(inner, Some(&Type::Float), ctx)?;
                        ctx.body.push(Instr::F64Neg);
                    }
                    (UnaryOp::Not, Type::Bool) => {
                        self.emit_expr(inner, Some(&Type::Bool), ctx)?;
                        ctx.body.push(Instr::I32Eqz);
                    }
                    _ => return Err(format!("unsupported unary {:?} on {:?}", op, ity)),
                }
            }
            Expr::Binary { op, left, right } => {
                if *op == BinOp::And {
                    self.emit_expr(left, Some(&Type::Bool), ctx)?;
                    ctx.body.push(Instr::If(BlockType::Val(ValType::I32)));
                    ctx.ctrl.push(CtrlKind::Plain);
                    self.emit_expr(right, Some(&Type::Bool), ctx)?;
                    ctx.body.push(Instr::Else);
                    ctx.body.push(Instr::I32Const(0));
                    ctx.ctrl.pop();
                    ctx.body.push(Instr::End);
                    return Ok(());
                }
                if *op == BinOp::Or {
                    self.emit_expr(left, Some(&Type::Bool), ctx)?;
                    ctx.body.push(Instr::If(BlockType::Val(ValType::I32)));
                    ctx.ctrl.push(CtrlKind::Plain);
                    ctx.body.push(Instr::I32Const(1));
                    ctx.body.push(Instr::Else);
                    self.emit_expr(right, Some(&Type::Bool), ctx)?;
                    ctx.ctrl.pop();
                    ctx.body.push(Instr::End);
                    return Ok(());
                }

                let operand_ty = ctx
                    .infer_type(left, self.hub)
                    .or_else(|| ctx.infer_type(right, self.hub))
                    .ok_or_else(|| "cannot infer binary operand type".to_string())?;

                self.emit_expr(left, Some(&operand_ty), ctx)?;
                self.emit_expr(right, Some(&operand_ty), ctx)?;

                match op {
                    BinOp::Eq => {
                        self.emit_val_eq_instrs(&operand_ty, &mut ctx.body)?;
                    }
                    BinOp::Ne => {
                        self.emit_val_eq_instrs(&operand_ty, &mut ctx.body)?;
                        ctx.body.push(Instr::I32Eqz);
                    }
                    BinOp::Add => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64Add),
                        Type::Float => ctx.body.push(Instr::F64Add),
                        Type::Str => ctx.body.push(Instr::Call(FN_STR_CONCAT)),
                        _ => return Err(format!("unsupported '+' on {:?}", operand_ty)),
                    },
                    BinOp::Sub => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64Sub),
                        Type::Float => ctx.body.push(Instr::F64Sub),
                        _ => return Err(format!("unsupported '-' on {:?}", operand_ty)),
                    },
                    BinOp::Mul => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64Mul),
                        Type::Float => ctx.body.push(Instr::F64Mul),
                        _ => return Err(format!("unsupported '*' on {:?}", operand_ty)),
                    },
                    BinOp::Div | BinOp::IntDiv => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64DivS),
                        Type::Float => ctx.body.push(Instr::F64Div),
                        _ => return Err(format!("unsupported '/' on {:?}", operand_ty)),
                    },
                    BinOp::Mod => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64RemS),
                        _ => return Err(format!("unsupported '%' on {:?}", operand_ty)),
                    },
                    BinOp::Lt => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64LtS),
                        Type::Float => ctx.body.push(Instr::F64Lt),
                        _ => return Err(format!("unsupported '<' on {:?}", operand_ty)),
                    },
                    BinOp::Le => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64LeS),
                        Type::Float => ctx.body.push(Instr::F64Le),
                        _ => return Err(format!("unsupported '<=' on {:?}", operand_ty)),
                    },
                    BinOp::Gt => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64GtS),
                        Type::Float => ctx.body.push(Instr::F64Gt),
                        _ => return Err(format!("unsupported '>' on {:?}", operand_ty)),
                    },
                    BinOp::Ge => match operand_ty {
                        Type::Int => ctx.body.push(Instr::I64GeS),
                        Type::Float => ctx.body.push(Instr::F64Ge),
                        _ => return Err(format!("unsupported '>=' on {:?}", operand_ty)),
                    },
                    BinOp::And | BinOp::Or => unreachable!(),
                }
            }
            Expr::Call { func, args } => {
                let &fidx = self
                    .user_fn_indices
                    .get(func)
                    .ok_or_else(|| format!("unknown function '{}'", func))?;
                let ptypes = self
                    .user_fn_sigs
                    .get(func)
                    .map(|(ps, _)| ps.clone())
                    .unwrap_or_default();
                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, ptypes.get(i), ctx)?;
                }
                ctx.body.push(Instr::Call(fidx));
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(x) => {
                    let xty = ctx
                        .infer_type(x, self.hub)
                        .ok_or_else(|| "cannot infer Len target type".to_string())?;
                    self.emit_expr(x, Some(&xty), ctx)?;
                    match xty {
                        Type::Str => {
                            ctx.body.push(Instr::I64Const(32));
                            ctx.body.push(Instr::I64ShrU);
                        }
                        Type::List(_) => {
                            ctx.body.push(Instr::I32Load(4));
                            ctx.body.push(Instr::I64ExtendI32S);
                        }
                        _ => return Err(format!("Len unsupported on {:?}", xty)),
                    }
                }
                Intrinsic::Min(a, b) => {
                    let ty = ctx.infer_type(a, self.hub).unwrap_or(Type::Int);
                    self.emit_expr(a, Some(&ty), ctx)?;
                    self.emit_expr(b, Some(&ty), ctx)?;
                    if ty == Type::Float {
                        ctx.body.push(Instr::F64Min);
                    } else {
                        ctx.body.push(Instr::Call(FN_I64_MIN));
                    }
                }
                Intrinsic::Max(a, b) => {
                    let ty = ctx.infer_type(a, self.hub).unwrap_or(Type::Int);
                    self.emit_expr(a, Some(&ty), ctx)?;
                    self.emit_expr(b, Some(&ty), ctx)?;
                    if ty == Type::Float {
                        ctx.body.push(Instr::F64Max);
                    } else {
                        ctx.body.push(Instr::Call(FN_I64_MAX));
                    }
                }
                Intrinsic::Abs(a) => {
                    let ty = ctx.infer_type(a, self.hub).unwrap_or(Type::Int);
                    self.emit_expr(a, Some(&ty), ctx)?;
                    if ty == Type::Float {
                        ctx.body.push(Instr::F64Abs);
                    } else {
                        ctx.body.push(Instr::Call(FN_I64_ABS));
                    }
                }
                Intrinsic::Push { list, value } => {
                    let lty = ctx
                        .infer_type(list, self.hub)
                        .ok_or_else(|| "cannot infer Push list type".to_string())?;
                    let Type::List(elem_ty) = lty else {
                        return Err("Push target is not a list".to_string());
                    };
                    let elem_vt = self.slot_val_type(&elem_ty)?;
                    let val_local = ctx.alloc_local(elem_vt);
                    let hdr_local = ctx.alloc_local(ValType::I32);
                    self.emit_expr(list, Some(&Type::List(elem_ty.clone())), ctx)?;
                    ctx.body.push(Instr::LocalSet(hdr_local));
                    self.emit_expr(value, Some(&elem_ty), ctx)?;
                    ctx.body.push(Instr::LocalSet(val_local));
                    ctx.body.push(Instr::LocalGet(hdr_local));
                    ctx.body.push(Instr::Call(FN_LIST_PUSH_SLOT));
                    ctx.body.push(Instr::LocalGet(val_local));
                    ctx.body.push(store_slot_instr(elem_vt, 0));
                }
                Intrinsic::Print(args) => {
                    for (idx, a) in args.iter().enumerate() {
                        if idx > 0 {
                            ctx.body.push(Instr::Call(FN_IMP_PRINT_SEP));
                        }
                        let aty = ctx.infer_type(a, self.hub).unwrap_or(Type::Int);
                        self.emit_expr(a, Some(&aty), ctx)?;
                        match aty {
                            Type::Int => ctx.body.push(Instr::Call(FN_IMP_PRINT_I64)),
                            Type::Float => ctx.body.push(Instr::Call(FN_IMP_PRINT_F64)),
                            Type::Bool => ctx.body.push(Instr::Call(FN_IMP_PRINT_BOOL)),
                            Type::Str => ctx.body.push(Instr::Call(FN_IMP_PRINT_STR)),
                            Type::Named(n) if self.enums.contains_key(&n) => {
                                ctx.body.push(Instr::Call(FN_IMP_PRINT_I64));
                            }
                            other => return Err(format!("Print unsupported on {:?}", other)),
                        }
                    }
                    ctx.body.push(Instr::Call(FN_IMP_PRINT_NL));
                }
                Intrinsic::Contains { haystack, needle } => {
                    let hty = ctx
                        .infer_type(haystack, self.hub)
                        .ok_or_else(|| "cannot infer Contains haystack type".to_string())?;
                    match hty {
                        Type::Str => {
                            self.emit_expr(haystack, Some(&Type::Str), ctx)?;
                            self.emit_expr(needle, Some(&Type::Str), ctx)?;
                            ctx.body.push(Instr::Call(FN_STR_CONTAINS));
                        }
                        Type::List(elem_ty) => {
                            let fidx = self.ensure_list_contains_fn(&elem_ty)?;
                            self.emit_expr(haystack, Some(&Type::List(elem_ty.clone())), ctx)?;
                            self.emit_expr(needle, Some(&elem_ty), ctx)?;
                            ctx.body.push(Instr::Call(fidx));
                        }
                        other => return Err(format!("Contains unsupported on {:?}", other)),
                    }
                }
                Intrinsic::Upper(s) => {
                    self.emit_expr(s, Some(&Type::Str), ctx)?;
                    ctx.body.push(Instr::Call(FN_STR_UPPER));
                }
                Intrinsic::Lower(s) => {
                    self.emit_expr(s, Some(&Type::Str), ctx)?;
                    ctx.body.push(Instr::Call(FN_STR_LOWER));
                }
                Intrinsic::ToStr(x) => {
                    let xty = ctx.infer_type(x, self.hub).unwrap_or(Type::Int);
                    self.emit_expr(x, Some(&xty), ctx)?;
                    match xty {
                        Type::Int => ctx.body.push(Instr::Call(FN_I64_TO_STR)),
                        Type::Float => ctx.body.push(Instr::Call(FN_IMP_TOSTR_F64)),
                        Type::Bool => ctx.body.push(Instr::Call(FN_BOOL_TO_STR)),
                        Type::Str => {}
                        Type::Named(n) if self.enums.contains_key(&n) => {
                            ctx.body.push(Instr::Call(FN_I64_TO_STR));
                        }
                        other => return Err(format!("ToStr unsupported on {:?}", other)),
                    }
                }
            },
        }
        Ok(())
    }

    fn encode_module(&self) -> WasmArtifact {
        // Deduplicate function type signatures
        let mut sigs: Vec<FuncSig> = Vec::new();
        let mut sig_map: HashMap<FuncSig, u32> = HashMap::new();
        let mut intern_sig = |s: &FuncSig| -> u32 {
            if let Some(&idx) = sig_map.get(s) {
                idx
            } else {
                let idx = sigs.len() as u32;
                sigs.push(s.clone());
                sig_map.insert(s.clone(), idx);
                idx
            }
        };

        let import_type_indices: Vec<u32> =
            self.imports.iter().map(|im| intern_sig(&im.sig)).collect();
        let def_type_indices: Vec<u32> =
            self.defined.iter().map(|df| intern_sig(&df.sig)).collect();

        let heap_base = ((BASE_DATA_OFFSET + self.data.len() as u32 + 15) & !7) as i32;

        let mut bytes = Vec::with_capacity(2048);
        bytes.extend_from_slice(b"\0asm");
        bytes.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

        // Section 1: Type
        let mut sec_type = Vec::new();
        push_u32(&mut sec_type, sigs.len() as u32);
        for sig in &sigs {
            sec_type.push(0x60);
            push_u32(&mut sec_type, sig.params.len() as u32);
            for p in &sig.params {
                sec_type.push(p.byte());
            }
            push_u32(&mut sec_type, sig.results.len() as u32);
            for r in &sig.results {
                sec_type.push(r.byte());
            }
        }
        push_section(&mut bytes, 1, &sec_type);

        // Section 2: Import
        let mut sec_imp = Vec::new();
        push_u32(&mut sec_imp, self.imports.len() as u32);
        for (im, &tidx) in self.imports.iter().zip(import_type_indices.iter()) {
            push_name(&mut sec_imp, im.module);
            push_name(&mut sec_imp, im.field);
            sec_imp.push(0x00); // func import
            push_u32(&mut sec_imp, tidx);
        }
        push_section(&mut bytes, 2, &sec_imp);

        // Section 3: Function
        let mut sec_func = Vec::new();
        push_u32(&mut sec_func, def_type_indices.len() as u32);
        for &tidx in &def_type_indices {
            push_u32(&mut sec_func, tidx);
        }
        push_section(&mut bytes, 3, &sec_func);

        // Section 5: Memory (min 16 pages = 1 MiB, growable)
        let mut sec_mem = Vec::new();
        push_u32(&mut sec_mem, 1);
        sec_mem.push(0x00); // limits: min only
        push_u32(&mut sec_mem, 16);
        push_section(&mut bytes, 5, &sec_mem);

        // Section 6: Global (`$heap_ptr: (mut i32)`)
        let mut sec_glob = Vec::new();
        push_u32(&mut sec_glob, 1);
        sec_glob.push(ValType::I32.byte());
        sec_glob.push(0x01); // mutable
        sec_glob.push(0x41); // i32.const
        push_sleb_i32(&mut sec_glob, heap_base);
        sec_glob.push(0x0B); // end
        push_section(&mut bytes, 6, &sec_glob);

        // Section 7: Export (`memory` + exported functions)
        let mut exports_list: Vec<(String, u8, u32)> = vec![("memory".to_string(), 0x02, 0)];
        for (i, df) in self.defined.iter().enumerate() {
            if let Some(exp) = &df.export_name {
                exports_list.push((exp.clone(), 0x00, (self.imports.len() + i) as u32));
            }
        }
        let mut sec_exp = Vec::new();
        push_u32(&mut sec_exp, exports_list.len() as u32);
        for (ename, kind, idx) in &exports_list {
            push_name(&mut sec_exp, ename);
            sec_exp.push(*kind);
            push_u32(&mut sec_exp, *idx);
        }
        push_section(&mut bytes, 7, &sec_exp);

        // Section 10: Code
        let mut sec_code = Vec::new();
        push_u32(&mut sec_code, self.defined.len() as u32);
        for df in &self.defined {
            let mut fn_bytes = Vec::new();
            let runs = compress_local_runs(&df.extra_locals);
            push_u32(&mut fn_bytes, runs.len() as u32);
            for (cnt, vt) in runs {
                push_u32(&mut fn_bytes, cnt);
                fn_bytes.push(vt.byte());
            }
            for ins in &df.body {
                encode_instr(ins, &mut fn_bytes);
            }
            fn_bytes.push(0x0B); // function body end
            push_u32(&mut sec_code, fn_bytes.len() as u32);
            sec_code.extend_from_slice(&fn_bytes);
        }
        let code_bytes = sec_code.len();
        push_section(&mut bytes, 10, &sec_code);

        // Section 11: Data
        if !self.data.is_empty() {
            let mut sec_data = Vec::new();
            push_u32(&mut sec_data, 1);
            sec_data.push(0x00); // active segment, memory 0
            sec_data.push(0x41); // i32.const
            push_sleb_i32(&mut sec_data, BASE_DATA_OFFSET as i32);
            sec_data.push(0x0B); // end
            push_u32(&mut sec_data, self.data.len() as u32);
            sec_data.extend_from_slice(&self.data);
            push_section(&mut bytes, 11, &sec_data);
        }

        let wat = self.format_wat(heap_base);
        let export_names: Vec<String> = exports_list.into_iter().map(|(n, _, _)| n).collect();

        WasmArtifact {
            bytes,
            wat,
            exports: export_names,
            code_bytes,
            data_bytes: self.data.len(),
            func_count: self.defined.len(),
        }
    }

    fn format_wat(&self, heap_base: i32) -> String {
        let mut fn_names: Vec<String> = self
            .imports
            .iter()
            .map(|im| im.wat_name.to_string())
            .collect();
        for df in &self.defined {
            fn_names.push(df.name.clone());
        }

        let mut w = String::new();
        w.push_str(";; Generated by StarLang Zero-Dependency WebAssembly 1.0 Backend\n");
        w.push_str("(module\n");
        for im in &self.imports {
            w.push_str(&format!(
                "  (import \"{}\" \"{}\" (func ${}{}))\n",
                im.module,
                im.field,
                im.wat_name,
                fmt_wat_sig(&im.sig)
            ));
        }
        w.push_str("  (memory (export \"memory\") 16)\n");
        w.push_str(&format!(
            "  (global $heap_ptr (mut i32) (i32.const {}))\n",
            heap_base
        ));
        if !self.data.is_empty() {
            w.push_str(&format!(
                "  (data (i32.const {}) \"{}\")\n",
                BASE_DATA_OFFSET,
                escape_wat_bytes(&self.data)
            ));
        }

        // Only emit full disassembly for user functions, tests, and struct/list helpers,
        // keeping fixed runtime intrinsics compact with a 1-line summary comment unless small.
        for (idx, df) in self.defined.iter().enumerate() {
            let fidx = (self.imports.len() + idx) as u32;
            let is_builtin_rt = (FN_ALLOC..=FN_LIST_SLOT_ADDR).contains(&fidx);
            let exp_clause = match &df.export_name {
                Some(en) => format!(" (export \"{}\")", en),
                None => String::new(),
            };
            w.push_str(&format!(
                "\n  (func ${}{}{}\n",
                df.name,
                exp_clause,
                fmt_wat_sig(&df.sig)
            ));
            if !df.extra_locals.is_empty() {
                let ls: Vec<&str> = df.extra_locals.iter().map(|t| t.wat()).collect();
                w.push_str(&format!("    (local {})\n", ls.join(" ")));
            }
            if is_builtin_rt {
                w.push_str(&format!(
                    "    ;; [native Wasm runtime helper: {} instructions]\n",
                    df.body.len()
                ));
            } else {
                let mut indent = 2usize;
                for ins in &df.body {
                    if matches!(ins, Instr::Else | Instr::End) {
                        indent = indent.saturating_sub(1);
                    }
                    let pad = "  ".repeat(indent);
                    w.push_str(&format!("{}{}\n", pad, fmt_wat_instr(ins, &fn_names)));
                    if matches!(
                        ins,
                        Instr::Block(_) | Instr::Loop(_) | Instr::If(_) | Instr::Else
                    ) {
                        indent += 1;
                    }
                }
            }
            w.push_str("  )\n");
        }
        w.push_str(")\n");
        w
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CtrlKind {
    Plain,
    LoopBreak,
    LoopContinue,
}

struct FnCodegen {
    param_count: u32,
    ret_ty: Type,
    extra_locals: Vec<ValType>,
    scopes: Vec<HashMap<String, (u32, Type)>>,
    list_hints: HashMap<String, Type>,
    ctrl: Vec<CtrlKind>,
    body: Vec<Instr>,
}

impl FnCodegen {
    fn new(param_count: u32, ret_ty: Type) -> Self {
        Self {
            param_count,
            ret_ty,
            extra_locals: Vec::new(),
            scopes: Vec::new(),
            list_hints: HashMap::new(),
            ctrl: Vec::new(),
            body: Vec::new(),
        }
    }

    fn alloc_local(&mut self, vt: ValType) -> u32 {
        let idx = self.param_count + self.extra_locals.len() as u32;
        self.extra_locals.push(vt);
        idx
    }

    fn define_var(&mut self, name: String, idx: u32, ty: Type) {
        if let Some(top) = self.scopes.last_mut() {
            top.insert(name, (idx, ty));
        }
    }

    fn lookup_var(&self, name: &str) -> Option<(u32, Type)> {
        for sc in self.scopes.iter().rev() {
            if let Some(found) = sc.get(name) {
                return Some(found.clone());
            }
        }
        None
    }

    fn flat_type_env(&self) -> HashMap<String, Type> {
        let mut env = HashMap::new();
        for sc in &self.scopes {
            for (k, (_, t)) in sc {
                env.insert(k.clone(), t.clone());
            }
        }
        env
    }

    fn infer_type(&self, expr: &Expr, hub: &HubModule) -> Option<Type> {
        let env = self.flat_type_env();
        infer_hub_expr_type(expr, &env, hub)
    }

    fn branch_depth(&self, target: CtrlKind) -> Option<u32> {
        for (i, kind) in self.ctrl.iter().enumerate().rev() {
            if *kind == target {
                return Some((self.ctrl.len() - 1 - i) as u32);
            }
        }
        None
    }

    fn collect_list_hints(&mut self, stmts: &[Stmt], hub: &HubModule) {
        let mut tmp_env = self.flat_type_env();
        collect_hints_rec(stmts, hub, &mut tmp_env, &mut self.list_hints);
    }
}

fn infer_hub_expr_type(expr: &Expr, env: &HashMap<String, Type>, hub: &HubModule) -> Option<Type> {
    let mut fn_ret_types = HashMap::new();
    let mut struct_fields = HashMap::new();
    let mut enum_names = HashSet::new();
    for item in &hub.items {
        match item {
            Item::Function(f) => {
                fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
            }
            Item::Struct(s) => {
                let mut fmap = HashMap::new();
                for fl in &s.fields {
                    fmap.insert(fl.name.clone(), fl.ty.clone());
                }
                struct_fields.insert(s.name.clone(), fmap);
            }
            Item::Enum(e) => {
                enum_names.insert(e.name.clone());
            }
            _ => {}
        }
    }
    infer_expr_type(expr, env, &fn_ret_types, &struct_fields, &enum_names)
}

fn collect_hints_rec(
    stmts: &[Stmt],
    hub: &HubModule,
    env: &mut HashMap<String, Type>,
    hints: &mut HashMap<String, Type>,
) {
    for s in stmts {
        match s {
            Stmt::Let {
                name, ty, value, ..
            } => {
                if let Some(t) = ty.clone().or_else(|| infer_hub_expr_type(value, env, hub)) {
                    env.insert(name.clone(), t);
                }
            }
            Stmt::Expr {
                expr: Expr::Intrinsic(intr),
                ..
            } => {
                if let Intrinsic::Push {
                    list: Expr::Var(v),
                    value,
                } = intr.as_ref()
                {
                    if let Some(et) = infer_hub_expr_type(value, env, hub) {
                        let lt = Type::List(Box::new(et));
                        hints.insert(v.clone(), lt.clone());
                        env.insert(v.clone(), lt);
                    }
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_hints_rec(then_body, hub, env, hints);
                collect_hints_rec(else_body, hub, env, hints);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_hints_rec(&a.body, hub, env, hints);
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForEach { body, .. } => {
                collect_hints_rec(body, hub, env, hints);
            }
            _ => {}
        }
    }
}

fn load_slot_instr(vt: ValType, offset: u32) -> Instr {
    match vt {
        ValType::I32 => Instr::I32Load(offset),
        ValType::I64 => Instr::I64Load(offset),
        ValType::F64 => Instr::F64Load(offset),
    }
}

fn store_slot_instr(vt: ValType, offset: u32) -> Instr {
    match vt {
        ValType::I32 => Instr::I32Store(offset),
        ValType::I64 => Instr::I64Store(offset),
        ValType::F64 => Instr::F64Store(offset),
    }
}

fn mangle_type(ty: &Type) -> String {
    match ty {
        Type::Int => "i64".to_string(),
        Type::Float => "f64".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "str".to_string(),
        Type::Void => "void".to_string(),
        Type::List(inner) => format!("list_{}", mangle_type(inner)),
        Type::Named(n) => n.clone(),
    }
}

fn compress_local_runs(locals: &[ValType]) -> Vec<(u32, ValType)> {
    let mut out: Vec<(u32, ValType)> = Vec::new();
    for &vt in locals {
        if let Some((cnt, prev)) = out.last_mut() {
            if *prev == vt {
                *cnt += 1;
                continue;
            }
        }
        out.push((1, vt));
    }
    out
}

fn push_u32(out: &mut Vec<u8>, mut val: u32) {
    loop {
        let mut byte = (val & 0x7F) as u8;
        val >>= 7;
        if val != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if val == 0 {
            break;
        }
    }
}

fn push_sleb_i32(out: &mut Vec<u8>, mut val: i32) {
    loop {
        let byte = (val & 0x7F) as u8;
        val >>= 7;
        let done = (val == 0 && (byte & 0x40) == 0) || (val == -1 && (byte & 0x40) != 0);
        if done {
            out.push(byte);
            break;
        } else {
            out.push(byte | 0x80);
        }
    }
}

fn push_sleb_i64(out: &mut Vec<u8>, mut val: i64) {
    loop {
        let byte = (val & 0x7F) as u8;
        val >>= 7;
        let done = (val == 0 && (byte & 0x40) == 0) || (val == -1 && (byte & 0x40) != 0);
        if done {
            out.push(byte);
            break;
        } else {
            out.push(byte | 0x80);
        }
    }
}

fn push_name(out: &mut Vec<u8>, name: &str) {
    push_u32(out, name.len() as u32);
    out.extend_from_slice(name.as_bytes());
}

fn push_section(out: &mut Vec<u8>, id: u8, payload: &[u8]) {
    out.push(id);
    push_u32(out, payload.len() as u32);
    out.extend_from_slice(payload);
}

fn encode_instr(ins: &Instr, out: &mut Vec<u8>) {
    match ins {
        Instr::Unreachable => out.push(0x00),
        Instr::Block(bt) => {
            out.push(0x02);
            out.push(bt.byte());
        }
        Instr::Loop(bt) => {
            out.push(0x03);
            out.push(bt.byte());
        }
        Instr::If(bt) => {
            out.push(0x04);
            out.push(bt.byte());
        }
        Instr::Else => out.push(0x05),
        Instr::End => out.push(0x0B),
        Instr::Br(d) => {
            out.push(0x0C);
            push_u32(out, *d);
        }
        Instr::BrIf(d) => {
            out.push(0x0D);
            push_u32(out, *d);
        }
        Instr::Return => out.push(0x0F),
        Instr::Call(f) => {
            out.push(0x10);
            push_u32(out, *f);
        }
        Instr::Drop => out.push(0x1A),
        Instr::Select => out.push(0x1B),

        Instr::LocalGet(i) => {
            out.push(0x20);
            push_u32(out, *i);
        }
        Instr::LocalSet(i) => {
            out.push(0x21);
            push_u32(out, *i);
        }
        Instr::GlobalGet(i) => {
            out.push(0x23);
            push_u32(out, *i);
        }
        Instr::GlobalSet(i) => {
            out.push(0x24);
            push_u32(out, *i);
        }

        Instr::I32Load(off) => {
            out.push(0x28);
            push_u32(out, 2);
            push_u32(out, *off);
        }
        Instr::I64Load(off) => {
            out.push(0x29);
            push_u32(out, 3);
            push_u32(out, *off);
        }
        Instr::F64Load(off) => {
            out.push(0x2B);
            push_u32(out, 3);
            push_u32(out, *off);
        }
        Instr::I32Load8U(off) => {
            out.push(0x2D);
            push_u32(out, 0);
            push_u32(out, *off);
        }
        Instr::I32Store(off) => {
            out.push(0x36);
            push_u32(out, 2);
            push_u32(out, *off);
        }
        Instr::I64Store(off) => {
            out.push(0x37);
            push_u32(out, 3);
            push_u32(out, *off);
        }
        Instr::F64Store(off) => {
            out.push(0x39);
            push_u32(out, 3);
            push_u32(out, *off);
        }
        Instr::I32Store8(off) => {
            out.push(0x3A);
            push_u32(out, 0);
            push_u32(out, *off);
        }
        Instr::MemorySize => {
            out.push(0x3F);
            out.push(0x00);
        }
        Instr::MemoryGrow => {
            out.push(0x40);
            out.push(0x00);
        }

        Instr::I32Const(v) => {
            out.push(0x41);
            push_sleb_i32(out, *v);
        }
        Instr::I64Const(v) => {
            out.push(0x42);
            push_sleb_i64(out, *v);
        }
        Instr::F64Const(v) => {
            out.push(0x44);
            out.extend_from_slice(&v.to_le_bytes());
        }

        Instr::I32Eqz => out.push(0x45),
        Instr::I32Eq => out.push(0x46),
        Instr::I32Ne => out.push(0x47),
        Instr::I32LtS => out.push(0x48),
        Instr::I32GtS => out.push(0x4A),
        Instr::I32LeS => out.push(0x4C),
        Instr::I32LeU => out.push(0x4D),
        Instr::I32GeS => out.push(0x4E),
        Instr::I32Add => out.push(0x6A),
        Instr::I32Sub => out.push(0x6B),
        Instr::I32Mul => out.push(0x6C),
        Instr::I32And => out.push(0x71),
        Instr::I32Shl => out.push(0x74),

        Instr::I64Eqz => out.push(0x50),
        Instr::I64Eq => out.push(0x51),
        Instr::I64Ne => out.push(0x52),
        Instr::I64LtS => out.push(0x53),
        Instr::I64GtS => out.push(0x55),
        Instr::I64LeS => out.push(0x57),
        Instr::I64GeS => out.push(0x59),
        Instr::I64Add => out.push(0x7C),
        Instr::I64Sub => out.push(0x7D),
        Instr::I64Mul => out.push(0x7E),
        Instr::I64DivS => out.push(0x7F),
        Instr::I64DivU => out.push(0x80),
        Instr::I64RemS => out.push(0x81),
        Instr::I64RemU => out.push(0x82),
        Instr::I64Or => out.push(0x84),
        Instr::I64Shl => out.push(0x86),
        Instr::I64ShrU => out.push(0x88),

        Instr::F64Eq => out.push(0x61),
        Instr::F64Ne => out.push(0x62),
        Instr::F64Lt => out.push(0x63),
        Instr::F64Gt => out.push(0x64),
        Instr::F64Le => out.push(0x65),
        Instr::F64Ge => out.push(0x66),
        Instr::F64Abs => out.push(0x99),
        Instr::F64Neg => out.push(0x9A),
        Instr::F64Add => out.push(0xA0),
        Instr::F64Sub => out.push(0xA1),
        Instr::F64Mul => out.push(0xA2),
        Instr::F64Div => out.push(0xA3),
        Instr::F64Min => out.push(0xA4),
        Instr::F64Max => out.push(0xA5),

        Instr::I32WrapI64 => out.push(0xA7),
        Instr::I64ExtendI32S => out.push(0xAC),
        Instr::I64ExtendI32U => out.push(0xAD),
    }
}

fn fmt_wat_sig(sig: &FuncSig) -> String {
    let mut s = String::new();
    if !sig.params.is_empty() {
        let ps: Vec<&str> = sig.params.iter().map(|p| p.wat()).collect();
        s.push_str(&format!(" (param {})", ps.join(" ")));
    }
    if !sig.results.is_empty() {
        let rs: Vec<&str> = sig.results.iter().map(|r| r.wat()).collect();
        s.push_str(&format!(" (result {})", rs.join(" ")));
    }
    s
}

fn escape_wat_bytes(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        if (0x20..=0x7E).contains(&b) && b != b'"' && b != b'\\' {
            s.push(b as char);
        } else {
            s.push_str(&format!("\\{:02x}", b));
        }
    }
    s
}

fn fmt_wat_instr(ins: &Instr, fn_names: &[String]) -> String {
    match ins {
        Instr::Unreachable => "unreachable".to_string(),
        Instr::Block(bt) => format!("block{}", bt.wat()),
        Instr::Loop(bt) => format!("loop{}", bt.wat()),
        Instr::If(bt) => format!("if{}", bt.wat()),
        Instr::Else => "else".to_string(),
        Instr::End => "end".to_string(),
        Instr::Br(d) => format!("br {}", d),
        Instr::BrIf(d) => format!("br_if {}", d),
        Instr::Return => "return".to_string(),
        Instr::Call(f) => {
            if let Some(n) = fn_names.get(*f as usize) {
                format!("call ${}", n)
            } else {
                format!("call {}", f)
            }
        }
        Instr::Drop => "drop".to_string(),
        Instr::Select => "select".to_string(),
        Instr::LocalGet(i) => format!("local.get {}", i),
        Instr::LocalSet(i) => format!("local.set {}", i),
        Instr::GlobalGet(i) => format!("global.get {}", i),
        Instr::GlobalSet(i) => format!("global.set {}", i),
        Instr::I32Load(0) => "i32.load".to_string(),
        Instr::I32Load(o) => format!("i32.load offset={}", o),
        Instr::I64Load(0) => "i64.load".to_string(),
        Instr::I64Load(o) => format!("i64.load offset={}", o),
        Instr::F64Load(0) => "f64.load".to_string(),
        Instr::F64Load(o) => format!("f64.load offset={}", o),
        Instr::I32Load8U(0) => "i32.load8_u".to_string(),
        Instr::I32Load8U(o) => format!("i32.load8_u offset={}", o),
        Instr::I32Store(0) => "i32.store".to_string(),
        Instr::I32Store(o) => format!("i32.store offset={}", o),
        Instr::I64Store(0) => "i64.store".to_string(),
        Instr::I64Store(o) => format!("i64.store offset={}", o),
        Instr::F64Store(0) => "f64.store".to_string(),
        Instr::F64Store(o) => format!("f64.store offset={}", o),
        Instr::I32Store8(0) => "i32.store8".to_string(),
        Instr::I32Store8(o) => format!("i32.store8 offset={}", o),
        Instr::MemorySize => "memory.size".to_string(),
        Instr::MemoryGrow => "memory.grow".to_string(),
        Instr::I32Const(v) => format!("i32.const {}", v),
        Instr::I64Const(v) => format!("i64.const {}", v),
        Instr::F64Const(v) => format!("f64.const {}", v),
        Instr::I32Eqz => "i32.eqz".to_string(),
        Instr::I32Eq => "i32.eq".to_string(),
        Instr::I32Ne => "i32.ne".to_string(),
        Instr::I32LtS => "i32.lt_s".to_string(),
        Instr::I32GtS => "i32.gt_s".to_string(),
        Instr::I32LeS => "i32.le_s".to_string(),
        Instr::I32LeU => "i32.le_u".to_string(),
        Instr::I32GeS => "i32.ge_s".to_string(),
        Instr::I32Add => "i32.add".to_string(),
        Instr::I32Sub => "i32.sub".to_string(),
        Instr::I32Mul => "i32.mul".to_string(),
        Instr::I32And => "i32.and".to_string(),
        Instr::I32Shl => "i32.shl".to_string(),
        Instr::I64Eqz => "i64.eqz".to_string(),
        Instr::I64Eq => "i64.eq".to_string(),
        Instr::I64Ne => "i64.ne".to_string(),
        Instr::I64LtS => "i64.lt_s".to_string(),
        Instr::I64GtS => "i64.gt_s".to_string(),
        Instr::I64LeS => "i64.le_s".to_string(),
        Instr::I64GeS => "i64.ge_s".to_string(),
        Instr::I64Add => "i64.add".to_string(),
        Instr::I64Sub => "i64.sub".to_string(),
        Instr::I64Mul => "i64.mul".to_string(),
        Instr::I64DivS => "i64.div_s".to_string(),
        Instr::I64DivU => "i64.div_u".to_string(),
        Instr::I64RemS => "i64.rem_s".to_string(),
        Instr::I64RemU => "i64.rem_u".to_string(),
        Instr::I64Or => "i64.or".to_string(),
        Instr::I64Shl => "i64.shl".to_string(),
        Instr::I64ShrU => "i64.shr_u".to_string(),
        Instr::F64Eq => "f64.eq".to_string(),
        Instr::F64Ne => "f64.ne".to_string(),
        Instr::F64Lt => "f64.lt".to_string(),
        Instr::F64Gt => "f64.gt".to_string(),
        Instr::F64Le => "f64.le".to_string(),
        Instr::F64Ge => "f64.ge".to_string(),
        Instr::F64Abs => "f64.abs".to_string(),
        Instr::F64Neg => "f64.neg".to_string(),
        Instr::F64Add => "f64.add".to_string(),
        Instr::F64Sub => "f64.sub".to_string(),
        Instr::F64Mul => "f64.mul".to_string(),
        Instr::F64Div => "f64.div".to_string(),
        Instr::F64Min => "f64.min".to_string(),
        Instr::F64Max => "f64.max".to_string(),
        Instr::I32WrapI64 => "i32.wrap_i64".to_string(),
        Instr::I64ExtendI32S => "i64.extend_i32_s".to_string(),
        Instr::I64ExtendI32U => "i64.extend_i32_u".to_string(),
    }
}
