pub mod c;
pub mod cpp;
pub mod go;
pub mod java;
pub mod python;
pub mod ruby;
pub mod rust;
pub mod star;
pub mod swift;
pub mod typescript;
pub mod zig;

use crate::lens::{LanguageLens, SpokeId};

pub fn all_lenses() -> Vec<Box<dyn LanguageLens>> {
    vec![
        Box::new(rust::RustLens),
        Box::new(zig::ZigLens),
        Box::new(c::CLens),
        Box::new(cpp::CppLens),
        Box::new(swift::SwiftLens),
        Box::new(java::JavaLens),
        Box::new(go::GoLens),
        Box::new(python::PythonLens),
        Box::new(ruby::RubyLens),
        Box::new(typescript::TypeScriptLens),
        Box::new(star::StarLens),
    ]
}

pub fn lens_for(id: SpokeId) -> Box<dyn LanguageLens> {
    match id {
        SpokeId::Rust => Box::new(rust::RustLens),
        SpokeId::Zig => Box::new(zig::ZigLens),
        SpokeId::C => Box::new(c::CLens),
        SpokeId::Cpp => Box::new(cpp::CppLens),
        SpokeId::Swift => Box::new(swift::SwiftLens),
        SpokeId::Java => Box::new(java::JavaLens),
        SpokeId::Go => Box::new(go::GoLens),
        SpokeId::Python => Box::new(python::PythonLens),
        SpokeId::Ruby => Box::new(ruby::RubyLens),
        SpokeId::TypeScript => Box::new(typescript::TypeScriptLens),
        SpokeId::Star => Box::new(star::StarLens),
    }
}

pub fn unescape_string(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut chars = raw.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('r') => out.push('\r'),
                Some('\\') => out.push('\\'),
                Some('"') => out.push('"'),
                Some('\'') => out.push('\''),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}
