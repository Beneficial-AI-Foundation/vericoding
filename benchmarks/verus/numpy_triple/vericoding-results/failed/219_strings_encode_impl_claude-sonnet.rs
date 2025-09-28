// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed UTF-8 encoding helper and added deterministic encoding support */
fn char_to_utf8_bytes(c: char) -> (result: Vec<u8>)
    ensures
        result.len() >= 1,
{
    let code_point = c as u32;
    let mut bytes = Vec::new();
    
    if code_point <= 0x7F {
        bytes.push(code_point as u8);
    } else if code_point <= 0x7FF {
        bytes.push((0xC0 | (code_point >> 6)) as u8);
        bytes.push((0x80 | (code_point & 0x3F)) as u8);
    } else if code_point <= 0xFFFF {
        bytes.push((0xE0 | (code_point >> 12)) as u8);
        bytes.push((0x80 | ((code_point >> 6) & 0x3F)) as u8);
        bytes.push((0x80 | (code_point & 0x3F)) as u8);
    } else {
        bytes.push((0xF0 | (code_point >> 18)) as u8);
        bytes.push((0x80 | ((code_point >> 12) & 0x3F)) as u8);
        bytes.push((0x80 | ((code_point >> 6) & 0x3F)) as u8);
        bytes.push((0x80 | (code_point & 0x3F)) as u8);
    }
    
    bytes
}

fn encode_string(s: Vec<char>) -> (result: Vec<u8>)
    ensures
        s.len() == 0 ==> result.len() == 0,
        s.len() > 0 ==> result.len() > 0,
        result.len() >= s.len(),
{
    let mut encoded = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            encoded.len() >= i,
        decreases s.len() - i
    {
        let char_bytes = char_to_utf8_bytes(s[i]);
        let mut j = 0;
        while j < char_bytes.len()
            invariant
                0 <= j <= char_bytes.len(),
                encoded.len() >= i + j,
            decreases char_bytes.len() - j
        {
            encoded.push(char_bytes[j]);
            j += 1;
        }
        i += 1;
    }
    
    encoded
}
// </vc-helpers>

// <vc-spec>
fn encode(a: Vec<Vec<char>>, encoding: Vec<char>, errors: Vec<char>) -> (result: Vec<Vec<u8>>)
    ensures
        result@.len() == a@.len(),
        /* Deterministic encoding: same input produces same output */
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() && a@[i] == a@[j] ==> result@[i] == result@[j],
        /* Empty strings encode to empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() == 0 ==> result@[i].len() == 0,
        /* Non-empty strings produce non-empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() > 0 ==> result@[i].len() > 0,
        /* For UTF-8 encoding, encoded size is at least the string length */
        forall|i: int| 0 <= i < a@.len() ==> result@[i].len() >= a@[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants to properly handle deterministic encoding requirements */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j].len() >= a@[j].len(),
            forall|j: int| 0 <= j < i && a@[j].len() == 0 ==> result@[j].len() == 0,
            forall|j: int| 0 <= j < i && a@[j].len() > 0 ==> result@[j].len() > 0,
            forall|j1: int, j2: int| 0 <= j1 < i && 0 <= j2 < i && a@[j1] == a@[j2] ==> result@[j1] == result@[j2],
        decreases a.len() - i
    {
        let encoded_string = encode_string(a[i].clone());
        result.push(encoded_string);
        
        assert(result.len() == i + 1);
        assert(result@[i] == encode_string(a[i].clone()));
        
        proof {
            let curr_idx = i as int;
            
            // Prove that the current string's encoding satisfies the properties
            assert(a@[curr_idx].len() == 0 ==> result@[curr_idx].len() == 0);
            assert(a@[curr_idx].len() > 0 ==> result@[curr_idx].len() > 0);
            assert(result@[curr_idx].len() >= a@[curr_idx].len());
            
            // Prove deterministic property for the current element with all previous elements
            assert(forall|j: int| 0 <= j < curr_idx && a@[j] == a@[curr_idx] ==> result@[j] == result@[curr_idx]);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}