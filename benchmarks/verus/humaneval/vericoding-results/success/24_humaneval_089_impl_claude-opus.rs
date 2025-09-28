// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn encrypt_char(c: char) -> char {
    if 'a' <= c && c <= 'z' {
        (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char
    } else if 'A' <= c && c <= 'Z' {
        (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn encrypt(s: Vec<char>) -> (result: Vec<char>)
    requires s@.len() >= 0
    ensures result@.len() == s@.len(),
            forall|i: int| 0 <= i < s@.len() ==> #[trigger] result@[i] == #[trigger] encrypt_char(#[trigger] s@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == encrypt_char(s@[j]),
        decreases s.len() - i
    {
        let c = s[i];
        let encrypted = if 'a' <= c && c <= 'z' {
            let offset = ((c as u8 - 'a' as u8 + 4) % 26) + 'a' as u8;
            offset as char
        } else if 'A' <= c && c <= 'Z' {
            let offset = ((c as u8 - 'A' as u8 + 4) % 26) + 'A' as u8;
            offset as char
        } else {
            c
        };
        result.push(encrypted);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}