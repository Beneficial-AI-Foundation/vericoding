// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function signature syntax and improved UTF-8 validation */
fn is_valid_utf8(bytes: Seq<u8>, start: int) -> (bool, int)
    ensures 
        valid: bool ==> 0 <= start <= next <= bytes.len(),
        !valid: bool ==> next == start + 1
{
    if start >= bytes.len() {
        (true, start)
    } else {
        let b0 = bytes[start] as u32;
        if b0 < 0x80 {
            (true, start + 1)
        } else if b0 & 0xE0 == 0xC0 {
            if start + 1 < bytes.len() {
                let b1 = bytes[start + 1] as u32;
                if b1 & 0xC0 == 0x80 {
                    (true, start + 2)
                } else {
                    (false, start + 1)
                }
            } else {
                (false, start + 1)
            }
        } else if b0 & 0xF0 == 0xE0 {
            if start + 2 < bytes.len() {
                let b1 = bytes[start + 1] as u32;
                let b2 = bytes[start + 2] as u32;
                if b1 & 0xC0 == 0x80 && b2 & 0xC0 == 0x80 {
                    (true, start + 3)
                } else {
                    (false, start + 1)
                }
            } else {
                (false, start + 1)
            }
        } else if b0 & 0xF8 == 0xF0 {
            if start + 3 < bytes.len() {
                let b1 = bytes[start + 1] as u32;
                let b2 = bytes[start + 2] as u32;
                let b3 = bytes[start + 3] as u32;
                if b1 & 0xC0 == 0x80 && b2 & 0xC0 == 0x80 && b3 & 0xC0 == 0x80 {
                    (true, start + 4)
                } else {
                    (false, start + 1)
                }
            } else {
                (false, start + 1)
            }
        } else {
            (false, start + 1)
        }
    }
}

fn decode_utf8_strict(bytes: Seq<u8>) -> Seq<char>
    requires 
        bytes.len() >= 0
    ensures 
        result.len() >= 0
{
    let mut i = 0;
    let mut chars = Seq::<char>::empty();
    
    while i < bytes.len()
        invariant 
            0 <= i <= bytes.len(),
            chars.len() >= 0
    {
        let (valid, next) = is_valid_utf8(bytes, i);
        if valid {
            let mut codepoint = 0u32;
            let b0 = bytes[i] as u32;
            
            if b0 < 0x80 {
                codepoint = b0;
            } else if b0 & 0xE0 == 0xC0 {
                let b1 = bytes[i + 1] as u32;
                codepoint = ((b0 & 0x1F) << 6) | (b1 & 0x3F);
            } else if b0 & 0xF0 == 0xE0 {
                let b1 = bytes[i + 1] as u32;
                let b2 = bytes[i + 2] as u32;
                codepoint = ((b0 & 0x0F) << 12) | ((b1 & 0x3F) << 6) | (b2 & 0x3F);
            } else if b0 & 0xF8 == 0xF0 {
                let b1 = bytes[i + 1] as u32;
                let b2 = bytes[i + 2] as u32;
                let b3 = bytes[i + 3] as u32;
                codepoint = ((b0 & 0x07) << 18) | ((b1 & 0x3F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F);
            }
            
            chars = chars.push(char::from_u32(codepoint).unwrap());
            i = next;
        } else {
            return Seq::<char>::empty();
        }
    }
    
    chars
}

fn decode_utf8_replace(bytes: Seq<u8>) -> Seq<char>
    requires 
        bytes.len() >= 0
    ensures 
        result.len() >= 0
{
    let mut i = 0;
    let mut chars = Seq::<char>::empty();
    
    while i < bytes.len()
        invariant 
            0 <= i <= bytes.len(),
            chars.len() >= 0
    {
        let (valid, next) = is_valid_utf8(bytes, i);
        if valid {
            let mut codepoint = 0u32;
            let b0 = bytes[i] as u32;
            
            if b0 < 0x80 {
                codepoint = b0;
            } else if b0 & 0xE0 == 0xC0 {
                let b1 = bytes[i + 1] as u32;
                codepoint = ((b0 & 0x1F) << 6) | (b1 & 0x3F);
            } else if b0 & 0xF0 == 0xE0 {
                let b1 = bytes[i + 1] as u32;
                let b2 = bytes[i + 2] as u32;
                codepoint = ((b0 & 0x0F) << 12) | ((b1 & 0x3F) << 6) | (b2 & 0x3F);
            } else if b0 & 0xF8 == 0xF0 {
                let b1 = bytes[i + 1] as u32;
                let b2 = bytes[i + 2] as u32;
                let b3 = bytes[i + 3] as u32;
                codepoint = ((b0 & 0x07) << 18) | ((b1 & 0x3F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F);
            }
            
            chars = chars.push(char::from_u32(codepoint).unwrap());
            i = next;
        } else {
            chars = chars.push('\u{FFFD}');
            i = i + 1;
        }
    }
    
    chars
}

fn decode_ascii(bytes: Seq<u8>) -> Seq<char>
    requires 
        bytes.len() >= 0
    ensures 
        result.len() >= 0
{
    let mut chars = Seq::<char>::empty();
    let mut i = 0;
    
    while i < bytes.len()
        invariant 
            0 <= i <= bytes.len(),
            chars.len() >= 0
    {
        let byte = bytes[i] as u32;
        if byte < 128 {
            chars = chars.push(char::from_u32(byte).unwrap());
        } else {
            chars = chars.push('\u{FFFD}');
        }
        i = i + 1;
    }
    
    chars
}
// </vc-helpers>

// <vc-spec>
fn decode(a: Vec<Vec<u8>>, encoding: &str, errors: &str) -> (result: Vec<String>)
    requires 
        encoding == "utf-8" || encoding == "ascii",
        errors == "strict" || errors == "ignore" || errors == "replace",
        forall|i: int| 0 <= i < a.len() as int ==> a[i]@.len() >= 0,
    ensures
        result.len() as int == a.len() as int,
        forall|i: int| 0 <= i < a.len() as int ==> (
            /* Basic well-formedness: decoded strings are valid */
            result[i]@.len() >= 0 &&
            
            /* Deterministic behavior: identical inputs produce identical outputs */
            (forall|j: int| 0 <= j < a.len() as int && a[i]@ == a[j]@ ==> result[i]@ == result[j]@) &&
            
            /* Empty byte arrays decode to empty strings */
            (a[i]@.len() == 0 ==> result[i]@.len() == 0) &&
            
            /* Identity property: encoding then decoding with same parameters is identity for valid strings */
            (encoding == "utf-8" ==> true) &&
            
            /* Error handling consistency: strict mode fails on invalid sequences */
            (errors == "strict" ==> true) &&
            
            /* Length relationship: non-empty valid byte arrays produce strings */
            (a[i]@.len() > 0 && encoding == "utf-8" ==> (
                result[i]@.len() > 0 || errors != "strict"
            ))
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed return type specification and improved loop invariants */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> (
                result[j]@.len() >= 0 &&
                (a[j]@.len() == 0 ==> result[j]@.len() == 0) &&
                (forall|k: int| 0 <= k < i && a[j]@ == a[k]@ ==> result[j]@ == result[k]@)
            )
    {
        let bytes = a[i].clone();
        let decoded_chars = 
            if encoding == "utf-8" {
                if errors == "strict" {
                    decode_utf8_strict(bytes@)
                } else if errors == "replace" {
                    decode_utf8_replace(bytes@)
                } else { // ignore
                    decode_utf8_replace(bytes@)
                }
            } else { // ascii
                decode_ascii(bytes@)
            };
        
        let decoded_string = String::from_chars(decoded_chars);
        result.push(decoded_string);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}