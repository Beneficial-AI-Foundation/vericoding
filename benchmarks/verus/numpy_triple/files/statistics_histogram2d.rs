// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn histogram2d(x: &Vec<i32>, y: &Vec<i32>, bins: usize) -> (result: (Vec<Vec<usize>>, Vec<i32>, Vec<i32>))
    requires 
        x.len() == y.len(),
        bins > 0,
    ensures
        result.0.len() == bins,
        forall|i: int| 0 <= i < bins ==> result.0[i].len() == bins,
        result.1.len() == bins + 1,
        result.2.len() == bins + 1,
        forall|i: int, j: int| 0 <= i < bins && 0 <= j < bins ==> result.0[i][j] <= x.len(),
        forall|i: int| 0 <= i < bins ==> #[trigger] result.1[i] <= result.1[i + 1],
        forall|i: int| 0 <= i < bins ==> #[trigger] result.2[i] <= result.2[i + 1],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}