use std::collections::BTreeMap;

pub fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Minimal parser for flat JSON string objects like `{"spoke":"python","source":"..."}`.
pub fn parse_flat_json_object(body: &str) -> Result<BTreeMap<String, String>, String> {
    let chars: Vec<char> = body.chars().collect();
    let mut i = 0;
    let skip_ws = |idx: &mut usize| {
        while *idx < chars.len() && chars[*idx].is_whitespace() {
            *idx += 1;
        }
    };

    let parse_str = |idx: &mut usize| -> Result<String, String> {
        if *idx >= chars.len() || chars[*idx] != '"' {
            return Err("expected '\"'".to_string());
        }
        *idx += 1;
        let mut s = String::new();
        while *idx < chars.len() {
            let c = chars[*idx];
            *idx += 1;
            if c == '"' {
                return Ok(s);
            }
            if c == '\\' {
                if *idx >= chars.len() {
                    return Err("unterminated escape".to_string());
                }
                let esc = chars[*idx];
                *idx += 1;
                match esc {
                    '"' => s.push('"'),
                    '\\' => s.push('\\'),
                    '/' => s.push('/'),
                    'n' => s.push('\n'),
                    'r' => s.push('\r'),
                    't' => s.push('\t'),
                    'b' => s.push('\u{0008}'),
                    'f' => s.push('\u{000c}'),
                    'u' => {
                        if *idx + 4 > chars.len() {
                            return Err("invalid \\uXXXX escape".to_string());
                        }
                        let hex: String = chars[*idx..*idx + 4].iter().collect();
                        *idx += 4;
                        let code = u32::from_str_radix(&hex, 16)
                            .map_err(|_| "invalid hex in \\uXXXX".to_string())?;
                        if let Some(ch) = char::from_u32(code) {
                            s.push(ch);
                        }
                    }
                    other => s.push(other),
                }
            } else {
                s.push(c);
            }
        }
        Err("unterminated JSON string".to_string())
    };

    skip_ws(&mut i);
    if i >= chars.len() || chars[i] != '{' {
        return Err("expected '{'".to_string());
    }
    i += 1;
    let mut map = BTreeMap::new();

    loop {
        skip_ws(&mut i);
        if i < chars.len() && chars[i] == '}' {
            return Ok(map);
        }
        let key = parse_str(&mut i)?;
        skip_ws(&mut i);
        if i >= chars.len() || chars[i] != ':' {
            return Err("expected ':'".to_string());
        }
        i += 1;
        skip_ws(&mut i);
        let val = parse_str(&mut i)?;
        map.insert(key, val);
        skip_ws(&mut i);
        if i < chars.len() && chars[i] == ',' {
            i += 1;
            continue;
        }
        if i < chars.len() && chars[i] == '}' {
            return Ok(map);
        }
        return Err("expected ',' or '}'".to_string());
    }
}
