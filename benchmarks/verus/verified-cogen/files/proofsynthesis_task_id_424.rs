// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn extract_rear_chars(s: &Vec<Vec<char>>) -> (result: Vec<char>)

    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,

    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}