// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn getdomain(x: Vec<i32>) -> (result: Vec<i32>)
    requires x.len() > 0,
    ensures
        result.len() == 2,
        result[0] <= result[1],
        forall|i: int| 0 <= i < x.len() ==> result[0] <= x[i] && x[i] <= result[1],
        exists|i: int| 0 <= i < x.len() && x[i] == result[0],
        exists|j: int| 0 <= j < x.len() && x[j] == result[1],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}