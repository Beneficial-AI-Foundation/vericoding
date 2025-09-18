// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn condition_number(x: Vec<Vec<i32>>) -> (result: i32)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() == x.len(),
    ensures 
        result >= 0,
        result >= 1,
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