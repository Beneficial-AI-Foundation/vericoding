// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn id32(x: i32) -> i32 { x }
proof fn lemma_id32_monotone(a: i32, b: i32)
    ensures (a <= b) ==> (id32(a) <= id32(b))
{ }
proof fn lemma_id32_floor_bounds(x: i32)
    ensures id32(x) <= x, x < id32(x) + 1
{ }
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
    x
}
// </vc-code>

}
fn main() {}