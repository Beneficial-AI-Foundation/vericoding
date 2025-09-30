// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn encode_char(c: char) -> char {
    ((c as int - 'a' as int + 5) % 26 + 'a' as int) as char
}

spec fn decode_char(c: char) -> char {
    ((c as int - 'a' as int - 5) % 26 + 'a' as int) as char
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn encode_shift(s: Vec<char>) -> (t: Vec<char>)
    requires forall|i: int| 0 <= i < s@.len() ==> 'a' <= #[trigger] s@[i] <= 'z'
    ensures s@.len() == t@.len() && forall|i: int| 0 <= i < s@.len() ==> t@[i] == encode_char(s@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut t = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            t@.len() == i as int,
            forall|j: int| 0 <= j < i ==> t@[j] == encode_char(s@[j]),
            forall|j: int| 0 <= j < s@.len() ==> 'a' <= #[trigger] s@[j] <= 'z',
        decreases s.len() - i
    {
        let c = s[i];
        let encoded = ((c as u8 - 'a' as u8 + 5) % 26 + 'a' as u8) as char;
        t.push(encoded);
        i += 1;
    }
    t
}
// </vc-code>


}

fn main() {}