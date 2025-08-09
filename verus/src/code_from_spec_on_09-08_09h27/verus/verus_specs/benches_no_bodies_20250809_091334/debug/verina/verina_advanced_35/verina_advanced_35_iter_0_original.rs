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
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {}