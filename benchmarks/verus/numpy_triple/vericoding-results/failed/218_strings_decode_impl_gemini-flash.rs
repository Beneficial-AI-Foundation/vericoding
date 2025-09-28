// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a Verus-compatible string comparison function to address `core::str::traits::impl&%1::eq` incompatibility. */
pn_ghost_fn!{pub fn string_eq(s1: &str, s2: &str) -> bool { s1@.eq(s2@) }}
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
    /* code modified by LLM (iteration 5): Replaced `encoding.eq("...")` and `errors.eq("...")` with calls to the new `string_eq` helper to fix the compilation error. */
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result_vec.len() == i,
            result_vec.capacity() >= a.len(),
        decreases
            a.len() - i
    {
        let byte_array = &a[i];
        let decoded_string: String;

        if string_eq(encoding, "utf-8") {
            if string_eq(errors, "strict") {
                if byte_array.len() == 0 {
                    decoded_string = String::new();
                } else {
                    decoded_string = String::from_utf8(byte_array.clone()).unwrap();
                }
            } else if string_eq(errors, "ignore") {
                decoded_string = String::from_utf8_lossy(byte_array).to_string();
            } else if string_eq(errors, "replace") {
                decoded_string = String::from_utf8_lossy(byte_array).to_string();
            } else {
                decoded_string = String::new();
            }
        } else if string_eq(encoding, "ascii") {
            if string_eq(errors, "strict") {
                if byte_array.len() == 0 {
                    decoded_string = String::new();
                } else {
                    let mut ascii_valid = true;
                    for k in 0..byte_array.len() {
                        let b = byte_array[k];
                        if b > 127 {
                            ascii_valid = false;
                            break;
                        }
                    }
                    if ascii_valid {
                        decoded_string = String::from_utf8(byte_array.clone()).unwrap();
                    } else {
                        decoded_string = String::new();
                    }
                }
            } else if string_eq(errors, "ignore") {
                decoded_string = String::from_utf8_lossy(byte_array).to_string();
            } else if string_eq(errors, "replace") {
                decoded_string = String::from_utf8_lossy(byte_array).to_string();
            } else {
                decoded_string = String::new();
            }
        } else {
            decoded_string = String::new();
        }

        result_vec.push(decoded_string);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}