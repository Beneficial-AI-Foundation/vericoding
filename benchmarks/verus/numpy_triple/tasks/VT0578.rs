// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn corrcoef(x: Vec<i8>, y: Vec<i8>) -> (result: i8)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        exists|i: int, j: int| 0 <= i < x.len() && 0 <= j < x.len() && x[i] != x[j],
        exists|i: int, j: int| 0 <= i < y.len() && 0 <= j < y.len() && y[i] != y[j],
    ensures
        -100 <= result as int && result as int <= 100
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