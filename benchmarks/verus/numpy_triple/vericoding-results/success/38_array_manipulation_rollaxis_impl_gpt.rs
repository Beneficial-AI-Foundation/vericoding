// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_i32(a: i32, b: i32) -> i32 { if a < b { a } else { b } }
spec fn is_axis_valid(axis: i32, ndim: i32) -> bool { -ndim <= axis && axis < ndim }
proof fn lemma_reflexive_eq_int(x: int) ensures x == x { }
// </vc-helpers>

// <vc-spec>
fn numpy_rollaxis(a: Vec<f32>, axis: i32, start: i32) -> (result: Vec<f32>)
    ensures result == a
// </vc-spec>
// <vc-code>
{
    let result = a;
    result
}
// </vc-code>

}
fn main() {}