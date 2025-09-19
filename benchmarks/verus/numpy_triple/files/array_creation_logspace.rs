// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn logspace(start: i32, stop: i32, endpoint: bool, base: i32, num: usize) -> (result: Vec<i32>)
    requires 
        base > 0,
        base != 1,
        num > 0,
    ensures
        result.len() == num,
        forall|i: int| 0 <= i < num ==> result[i] > 0,
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