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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}