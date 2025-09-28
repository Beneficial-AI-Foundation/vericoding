// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_max(nums: Vec<i32>) -> (ret:i32)

    requires
        nums.len() > 0,

    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): Fixed compilation by using usize for latest_index and casting to int in invariants */
    let mut current_max = nums[0];
    let mut latest_index: usize = 0;
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            0 <= (latest_index as int) < nums@.len(),
            current_max == nums@[(latest_index as int)],
            forall |j: int| 0 <= j < (i as int) ==> nums@[j] <= current_max,
        decreases nums.len() - i
    {
        if current_max < nums[i] {
            current_max = nums[i];
            latest_index = i;
        } else if current_max == nums[i] {
            latest_index = i;
        }
        i += 1;
    }
    current_max
}
// </vc-code>

}
fn main() {}