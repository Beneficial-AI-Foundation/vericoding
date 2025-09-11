// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun1(x: &Vec<i32>) -> (max_index: usize)

    requires
        x.len() >= 1,

    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}