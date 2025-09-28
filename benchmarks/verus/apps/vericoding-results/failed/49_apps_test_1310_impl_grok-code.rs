// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32;

spec fn valid_input(arr: Seq<u32>) -> bool {
    arr.len() > 0
}

spec fn is_max_xor_subarray(arr: Seq<u32>, result: u32) -> bool
    recommends valid_input(arr)
{
    exists|i: int, j: int| 0 <= i <= j < arr.len() && result == xor_range(arr, i, j) &&
    forall|i1: int, j1: int| 0 <= i1 <= j1 < arr.len() ==> 
        (xor_range(arr, i1, j1) as int) <= (result as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added spec definition for xor_range to enable verification */
spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32
    requires 0 <= i <= j < arr.len()
    decreases (j - i) as int
{
    if i == j {
        arr[i]
    } else {
        arr[i] ^ xor_range(arr, i + 1, j)
    }
}

/* helper modified by LLM (iteration 4): Compute XOR from index i to j in the array recursively */
fn compute_xor(arr: &Vec<u32>, i: usize, j: usize) -> (result: u32)
    requires i <= j, j < arr.len()
    ensures result == xor_range(arr@, i as int, j as int)
    decreases j - i
{
    if i == j {
        arr[i]
    } else {
        arr[i] ^ compute_xor(arr, i + 1, j)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<u32>) -> (result: u32)
    requires valid_input(arr@)
    ensures is_max_xor_subarray(arr@, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Brute force check all subarrays for max XOR */
{
    let mut max_val: u32 = 0;
    for i in 0..arr.len() {
        for j in i..arr.len() {
            let xor_val = compute_xor(&arr, i, j);
            if xor_val > max_val {
                max_val = xor_val;
            }
        }
    }
    max_val
}
// </vc-code>


}

fn main() {}