// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn encode_char(c: char) -> char {
    ((c as int - 'a' as int + 5) % 26 + 'a' as int) as char
}

spec fn decode_char(c: char) -> char {
    ((c as int - 'a' as int - 5) % 26 + 'a' as int) as char
}

spec fn valid_char(c: char) -> bool {
    'a' <= c <= 'z'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn decode_shift(s: Vec<char>) -> (t: Vec<char>)
    requires forall|i: int| 0 <= i < s.len() ==> valid_char(s[i])
    ensures s.len() == t.len(),
            forall|i: int| 0 <= i < s.len() ==> t[i] == decode_char(s[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add decreases clause to while loop */
    let mut t = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            t.len() == i,
            forall|j: int| 0 <= j < i ==> t[j] == decode_char(s[j]),
            forall|j: int| 0 <= j < s.len() ==> valid_char(s[j]),
        decreases s.len() - i
    {
        let c = s[i];
        let c_val = c as u8;
        let a_val = 'a' as u8;
        let decoded_val = ((c_val - a_val + 21) % 26 + a_val) as char;
        t.push(decoded_val);
        i += 1;
    }
    t
}
// </vc-code>


}

fn main() {}