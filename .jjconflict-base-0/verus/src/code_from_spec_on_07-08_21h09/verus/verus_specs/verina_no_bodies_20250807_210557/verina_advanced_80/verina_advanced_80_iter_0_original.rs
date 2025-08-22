use vstd::prelude::*;

verus! {

// Precondition for twoSum
spec fn two_sum_precond(nums: Seq<i32>, target: i32) -> bool {
    // The array must have at least 2 elements
    nums.len() >= 2 &&
    
    // There exists exactly one pair of indices whose values sum to the target
    exists|i: int, j: int| 
        0 <= i < nums.len() && 
        0 <= j < i && 
        nums[i] + nums[j] == target &&
        
    // No other pair sums to the target (ensuring uniqueness)
    forall|i1: int, j1: int, i2: int, j2: int|
        (0 <= i1 < nums.len() && 0 <= j1 < i1 && nums[i1] + nums[j1] == target) &&
        (0 <= i2 < nums.len() && 0 <= j2 < i2 && nums[i2] + nums[j2] == target) ==>
        (i1 == i2 && j1 == j2)
}

// Postcondition for twoSum
spec fn two_sum_postcond(nums: Seq<i32>, target: i32, result: Seq<usize>) -> bool {
    // Result contains exactly 2 indices
    result.len() == 2 &&
    
    // The indices are valid (within bounds of the nums array)
    result[0] < nums.len() &&
    result[1] < nums.len() &&
    
    // The indices are in ascending order (sorted)
    result[0] < result[1] &&
    
    // The values at these indices sum to the target
    nums[result[0] as int] + nums[result[1] as int] == target
}

fn two_sum(nums: Vec<i32>, target: i32) -> (result: Vec<usize>)
    requires 
        two_sum_precond(nums@, target),
        // Add bounds to prevent overflow
        forall|i: int| 0 <= i < nums@.len() ==> nums@[i] >= -1000000000 && nums@[i] <= 1000000000,
        target >= -2000000000 && target <= 2000000000
    ensures two_sum_postcond(nums@, target, result@)
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

// Theorem statement (proof left as external)
#[verifier::external]
proof fn two_sum_spec_satisfied(nums: Seq<i32>, target: i32)
    requires two_sum_precond(nums, target)
    ensures 
        forall|result: Seq<usize>| 
            result.len() == 2 ==> 
            two_sum_postcond(nums, target, result)
{
    // Proof would go here - left as external for now
}

fn main() {}

} // verus!