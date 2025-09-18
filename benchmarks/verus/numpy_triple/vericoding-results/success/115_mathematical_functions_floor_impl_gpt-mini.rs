// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn le_and_lt_plus_one_implies_eq(a: i32, b: i32) requires a <= b && b < a + 1 ensures a == b { }
spec fn vec_idx_id(x: Vec<i32>) -> bool { forall|i: int| 0 <= i < x.len() ==> x[i] == x[i] }
// </vc-helpers>

// <vc-spec>
fn numpy_floor(x: Vec<i32>) -> (result: Vec<i32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x[i],
        forall|i: int| 0 <= i < result.len() ==> x[i] < result[i] + 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && x[i] <= x[j] ==> result[i] <= result[j],
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i]
// </vc-spec>
// <vc-code>
{
    let result = x;
    result
}
// </vc-code>

}
fn main() {}