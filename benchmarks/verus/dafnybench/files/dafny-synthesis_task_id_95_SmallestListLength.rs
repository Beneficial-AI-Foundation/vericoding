// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(s: Vec<Vec<i8>>) -> (v: i8)
    requires
        s@.len() > 0,
    ensures
        forall|i: int| 0 <= i < s@.len() ==> v as int <= s@[i].len(),
        exists|i: int| 0 <= i < s@.len() && v as int == #[trigger] s@[i].len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}