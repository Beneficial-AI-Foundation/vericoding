use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn max_in_range(seq: Seq<i32>, start: usize, end: usize, current_max: usize) 
    requires
        0 <= start <= end <= seq.len(),
        0 <= current_max < seq.len(),
        forall|i: int| start <= i && i < end ==> seq[i] <= seq[current_max as int],
    ensures
        forall|i: int| 0 <= i && i < end ==> seq[i] <= seq[current_max as int],
{
    if start > 0 {
        assert forall|i: int| 0 <= i && i < end implies seq[i] <= seq[current_max as int] by {
            let j = i;
            if j >= start {
                assert(seq[j] <= seq[current_max as int]);
            } else {
                assert(seq[j] <= seq[current_max as int]);
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn max_array(nums: &[i32]) -> (idx: usize)
    // pre-conditions-start
    requires
        nums.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut idx: usize = 0;
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            0 <= idx < nums.len(),
            i <= nums.len(),
            forall|j: int| 0 <= j && j < i ==> nums[j] <= nums[idx as int],
    {
        if nums[i] > nums[idx] {
            idx = i;
        }
        i += 1;
        
        proof {
            max_in_range(nums@, 0, i, idx);
        }
    }
    
    assert forall|j: int| 0 <= j && j < nums.len() implies nums[j] <= nums[idx as int] by {
        max_in_range(nums@, 0, nums.len(), idx);
    };
    
    idx
}
// </vc-code>

fn main() {}
}