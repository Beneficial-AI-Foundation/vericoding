// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}