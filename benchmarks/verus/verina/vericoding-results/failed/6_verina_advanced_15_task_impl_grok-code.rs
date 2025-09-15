// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{/* code modified by LLM (iteration 3): fixed invariants by limiting exists to prefix */    if nums.len() < 3 {
        return false;
    }
    let mut smallest = i32::MAX;
    let mut second = i32::MAX;
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            smallest == i32::MAX || exists|i_: int| 0 <= i_ < i && nums[i_] == smallest,
            second == i32::MAX || exists|i_: int| 0 <= i_ < i && nums[i_] == second,
            second == i32::MAX || smallest < second,
        decreases nums.len() - i,
    {
        let num = nums[i];
        if num <= smallest {
            smallest = num;
        } else if num <= second {
            second = num;
            proof {
                assert(num > smallest);
                assert(smallest < second);
            }
        } else {
            return true;
        }
        i += 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}