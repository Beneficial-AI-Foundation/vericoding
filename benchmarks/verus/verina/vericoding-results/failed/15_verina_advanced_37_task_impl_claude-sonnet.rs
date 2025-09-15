// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors in proof functions */
spec fn valid_majority_element(nums: Seq<i32>, candidate: i32) -> bool {
    let n = nums.len();
    count_occurrences(nums, candidate) > n / 2
}

proof fn majority_disjoint(nums: Seq<i32>, x: i32, y: i32)
    requires 
        x != y
    ensures 
        count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len()
{
    let filtered_x = nums.filter(|v: i32| v == x);
    let filtered_y = nums.filter(|v: i32| v == y);
    let filtered_xy = nums.filter(|v: i32| v == x || v == y);
    
    assert forall|i: int| 0 <= i < filtered_xy.len() implies #[
trigger filtered_xy[i]
] {
        filtered_xy[i] == x || filtered_xy[i] == y
    } by {
        // Each element in filtered_xy satisfies the filter condition
    };
    assert(filtered_x.len() + filtered_y.len() <= filtered_xy.len());
    assert(filtered_xy.len() <= nums.len());
}

proof fn majority_exists(nums: Seq<i32>) -> (maj: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2
    ensures 
        count_occurrences(nums, maj) > nums.len() / 2
{
    // Use choose to extract the majority element
    choose|x: i32| count_occurrences(nums, x) > nums.len() / 2
}

proof fn boyer_moore_correctness(nums: Seq<i32>, maj: i32)
    requires 
        nums.len() > 0,
        count_occurrences(nums, maj) > nums.len() / 2
    ensures 
        exists|candidate: i32| {
            let count_diff = count_occurrences(nums, candidate) - (nums.len() - count_occurrences(nums, candidate));
            count_diff > 0
        }
{
    let maj_count = count_occurrences(nums, maj);
    let other_count = nums.len() - maj_count;
    assert(maj_count > nums.len() / 2);
    assert(maj_count > other_count);
}
// </vc-helpers>

// <vc-spec>
fn majority_element(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures ({
        let nums_seq = nums@;
        let n = nums_seq.len();
        count_occurrences(nums_seq, result) > n / 2 &&
        forall|x: i32| x == result || count_occurrences(nums_seq, x) <= n / 2
    }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assert forall syntax error */
    let mut candidate = nums[0];
    let mut count: i32 = 0;
    
    for i in 0..nums.len()
        invariant
            0 <= i <= nums.len(),
            count >= -((i as i32))
    {
        if count == 0 {
            candidate = nums[i];
            count = 1;
        } else if nums[i] == candidate {
            if count < i32::MAX {
                count = count + 1;
            }
        } else {
            count = count - 1;
        }
    }
    
    proof {
        let nums_seq = nums@;
        let n = nums_seq.len();
        
        // Since majority element exists by precondition (implicit)
        assert(exists|maj: i32| count_occurrences(nums_seq, maj) > n / 2);
        
        // Extract the majority element
        let maj = majority_exists(nums_seq);
        
        // Boyer-Moore finds a valid candidate
        boyer_moore_correctness(nums_seq, maj);
        
        // The candidate must be the majority element
        assert(count_occurrences(nums_seq, candidate) > n / 2);
        
        // Prove uniqueness property
        assert forall|x: i32| x != candidate implies {
            majority_disjoint(nums_seq, candidate, x);
            count_occurrences(nums_seq, x) <= n / 2
        } by {
            majority_disjoint(nums_seq, candidate, x);
        };
    }
    
    candidate
}
// </vc-code>

}
fn main() {}