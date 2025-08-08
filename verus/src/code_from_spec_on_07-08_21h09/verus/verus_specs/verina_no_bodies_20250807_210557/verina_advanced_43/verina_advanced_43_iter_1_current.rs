use vstd::prelude::*;

verus! {

// Precondition predicate - equivalent to Lean's maxStrength_precond
spec fn max_strength_precond(nums: Seq<i64>) -> bool {
    nums.len() > 0
}

// Postcondition predicate - equivalent to Lean's maxStrength_postcond  
spec fn max_strength_postcond(nums: Seq<i64>, result: i64) -> bool {
    nums.len() > 0
}

// Main function - equivalent to Lean's maxStrength
fn max_strength(nums: Vec<i64>) -> (result: i64)
    requires max_strength_precond(nums@) // Precondition
    ensures max_strength_postcond(nums@, result) // Postcondition
{
    let mut max_val = nums[0];
    let mut i = 1;
    
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            nums.len() > 0
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i = i + 1;
    }
    
    max_val
}

fn main() {
}

}