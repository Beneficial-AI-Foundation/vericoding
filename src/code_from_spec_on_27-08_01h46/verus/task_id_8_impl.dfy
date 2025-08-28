use vstd::prelude::*;


verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    // pre-conditions-start
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == nums@[k as usize] * nums@[k as usize],
        decreases nums.len() - i
    {
        let squared_val = nums[i] * nums[i];
        result.push(squared_val);
        i = i + 1;
        proof {
            assert(result.len() == i);
            assert(result@[(i-1) as int] == nums@[(i-1) as int] * nums@[(i-1) as int]);
        }
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}