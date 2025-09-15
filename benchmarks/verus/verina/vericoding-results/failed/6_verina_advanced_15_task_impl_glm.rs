// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 4): fixed ghost variable declaration syntax */
    let n = nums.len() as int;
    if n < 3 {
        return false;
    }

    let mut first: i32 = i32::MAX;
    let mut second: i32 = i32::MAX;
    let ghost first_index: int = n;
    let ghost second_index: int = n;
    let ghost second_old_first_index: int = n;
    let ghost second_old_first_value: i32 = 0;

    for i in 0..n
        invariant
            0 <= first_index < i || first_index == n,
            0 <= second_index < i || second_index == n,
            second_index == n ==> second_old_first_index == n,
            second_index != n ==> {
                0 <= second_old_first_index < second_index,
                nums@[second_old_first_index] == second_old_first_value,
                second_old_first_value < second
            }
    {
        let num = nums[i];
        if num <= first {
            first = num;
            ghost {
                first_index = i;
            }
        } else if num <= second {
            second = num;
            ghost {
                second_index = i;
                second_old_first_index = first_index;
                second_old_first_value = first;
            }
        } else {
            return true;
        }
    }

    return false;
}
// </vc-code>

}
fn main() {}