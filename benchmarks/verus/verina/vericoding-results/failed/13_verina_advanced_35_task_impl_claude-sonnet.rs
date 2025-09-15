// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat 
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else {
        let first = nums[0];
        let rest_count = count_occurrences(nums.subrange(1, nums.len() as int), x);
        if first == x {
            rest_count + 1
        } else {
            rest_count
        }
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn majority_element_lemma(nums: Seq<i32>, candidate: i32)
    requires 
        nums.len() > 0,
        count_occurrences(nums, candidate) > nums.len() / 2,
    ensures 
        forall|x: i32| x != candidate ==> count_occurrences(nums, x) <= nums.len() / 2
{
    assert forall|x: i32| x != candidate implies {
        count_occurrences(nums, x) + count_occurrences(nums, candidate) <= nums.len()
    } by {
        let total_x = count_occurrences(nums, x);
        let total_candidate = count_occurrences(nums, candidate);
        assert(total_x + total_candidate <= nums.len());
    }
}

/* helper modified by LLM (iteration 5): fixed ghost type usage in executable code */
fn find_majority_linear(nums: Seq<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
    ensures 
        count_occurrences(nums, result) > nums.len() / 2
{
    let mut candidate = nums[0];
    let mut count = 1;
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant 
            1 <= i <= nums.len(),
            exists|x: i32| count_occurrences(nums, x) > nums.len() / 2
    {
        if nums[i as int] == candidate {
            count = count + 1;
        } else {
            if count > 1 {
                count = count - 1;
            } else {
                candidate = nums[i as int];
                count = 1;
            }
        }
        i = i + 1;
    }
    
    candidate
}
// </vc-helpers>

// <vc-spec>
fn majority_element(nums: Seq<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
    ensures 
        count_occurrences(nums, result) > nums.len() / 2,
        forall|x: i32| x != result ==> count_occurrences(nums, x) <= nums.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using helper function to find majority element */
    let candidate = find_majority_linear(nums);
    proof {
        majority_element_lemma(nums, candidate);
    }
    candidate
}
// </vc-code>

}
fn main() {}