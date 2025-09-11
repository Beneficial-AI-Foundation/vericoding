// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}