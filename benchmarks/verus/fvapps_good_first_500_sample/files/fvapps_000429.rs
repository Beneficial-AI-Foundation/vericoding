// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_turbulence_size(arr: Vec<i32>) -> (result: nat)
    requires arr.len() >= 1,
    ensures 
        1 <= result <= arr.len(),
        result >= 1,
        result <= arr.len(),
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
fn main() {
    // let test1 = vec![9, 4, 2, 10, 7, 8, 8, 1, 9];
    // assert(max_turbulence_size(test1) == 5);
    // 
    // let test2 = vec![4, 8, 12, 16];
    // assert(max_turbulence_size(test2) == 2);
    // 
    // let test3 = vec![100];
    // assert(max_turbulence_size(test3) == 1);
}