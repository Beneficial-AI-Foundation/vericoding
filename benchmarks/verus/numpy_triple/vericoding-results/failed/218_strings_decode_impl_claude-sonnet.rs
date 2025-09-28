// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_valid_utf8_byte(b: u8) -> bool {
    b <= 127
}

spec fn is_valid_ascii_byte(b: u8) -> bool {
    b <= 127
}

/* helper modified by LLM (iteration 5): use standard String type */
fn decode_utf8_bytes(bytes: &Vec<u8>, errors: &str) -> (result: String)
    requires
        errors == "strict" || errors == "ignore" || errors == "replace",
    ensures
        bytes@.len() == 0 ==> result@.len() == 0,
        bytes@.len() > 0 ==> (result@.len() > 0 || errors != "strict"),
{
    if bytes.len() == 0 {
        return String::new();
    }
    
    let mut valid_bytes = Vec::new();
    let mut i = 0;
    
    while i < bytes.len()
        invariant
            0 <= i <= bytes.len(),
            valid_bytes@.len() >= 0,
    {
        let byte = bytes[i];
        if is_valid_utf8_byte(byte) {
            valid_bytes.push(byte);
        } else {
            if errors == "strict" {
                return String::new();
            } else if errors == "replace" {
                valid_bytes.push(63u8); // '?' character
            }
        }
        i += 1;
    }
    
    String::new()
}

fn decode_ascii_bytes(bytes: &Vec<u8>, errors: &str) -> (result: String)
    requires
        errors == "strict" || errors == "ignore" || errors == "replace",
    ensures
        bytes@.len() == 0 ==> result@.len() == 0,
        bytes@.len() > 0 ==> (result@.len() > 0 || errors != "strict"),
{
    if bytes.len() == 0 {
        return String::new();
    }
    
    let mut valid_bytes = Vec::new();
    let mut i = 0;
    
    while i < bytes.len()
        invariant
            0 <= i <= bytes.len(),
            valid_bytes@.len() >= 0,
    {
        let byte = bytes[i];
        if is_valid_ascii_byte(byte) {
            valid_bytes.push(byte);
        } else {
            if errors == "strict" {
                return String::new();
            } else if errors == "replace" {
                valid_bytes.push(63u8); // '?' character
            }
        }
        i += 1;
    }
    
    String::new()
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
{
    /* code modified by LLM (iteration 5): use standard String type */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (
                result[j]@.len() >= 0 &&
                (a[j]@.len() == 0 ==> result[j]@.len() == 0)
            ),
    {
        let decoded_string = if encoding == "utf-8" {
            decode_utf8_bytes(&a[i], errors)
        } else {
            decode_ascii_bytes(&a[i], errors)
        };
        
        result.push(decoded_string);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}