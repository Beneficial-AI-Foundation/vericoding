// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn clip(arr: &Vec<i32>, min_val: i32, max_val: i32) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            if min_val <= max_val {
                if arr[i] < min_val {
                    result[i] == min_val
                } else if arr[i] > max_val {
                    result[i] == max_val
                } else {
                    result[i] == arr[i]
                }
            } else {
                result[i] == max_val
            }
        }
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