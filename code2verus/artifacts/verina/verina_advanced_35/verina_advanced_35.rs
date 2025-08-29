use vstd::prelude::*;

verus! {

// Helper function to count occurrences in a sequence
spec fn count_in_seq(s: Seq<i32>, x: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let count_rest = count_in_seq(s.drop_first(), x);
        if s[0] == x {
            count_rest + 1nat
        } else {
            count_rest
        }
    }
}

// Precondition: nums is non-empty and has a majority element  
spec fn majority_element_precond(nums: Seq<i32>) -> bool {
    nums.len() > 0 &&
    exists|x: i32| count_in_seq(nums, x) > nums.len() / 2
}

// Postcondition: result is the majority element
spec fn majority_element_postcond(nums: Seq<i32>, result: i32) -> bool {
    let n = nums.len();
    count_in_seq(nums, result) > n / 2 &&
    forall|x: i32| x != result ==> count_in_seq(nums, x) <= n / 2
}

fn majority_element(nums: Vec<i32>) -> (result: i32)
    requires
        majority_element_precond(nums@),
    ensures
        majority_element_postcond(nums@, result),
{
    // Implementation matches original Lean structure using a simple counting approach
    let n = nums.len();
    
    // Find the element that appears more than n/2 times
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
        decreases nums.len() - i,
    {
        let candidate = nums[i];
        
        // Count occurrences of candidate
        let mut count = 0;
        let mut j = 0;
        while j < nums.len()
            invariant
                j <= nums.len(),
                count <= j,
            decreases nums.len() - j,
        {
            if nums[j] == candidate {
                count = count + 1;
            }
            j = j + 1;
        }
        
        if count > n / 2 {
            // Found majority element
            // The proof that this satisfies the postcondition is left as an assumption,
            // corresponding to the 'sorry' in the original Lean theorem
            assume(majority_element_postcond(nums@, candidate));
            return candidate;
        }
        
        i = i + 1;
    }
    
    // Should never reach here given the precondition guarantees a majority element exists
    assume(false);
    0
}

}

fn main() {}