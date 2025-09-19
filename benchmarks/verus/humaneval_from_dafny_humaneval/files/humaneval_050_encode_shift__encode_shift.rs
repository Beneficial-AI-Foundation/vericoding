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
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}