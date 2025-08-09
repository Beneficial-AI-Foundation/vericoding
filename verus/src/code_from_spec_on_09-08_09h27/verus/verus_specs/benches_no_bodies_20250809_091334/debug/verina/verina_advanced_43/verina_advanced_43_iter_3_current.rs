use vstd::prelude::*;

verus! {

// Precondition predicate - equivalent to Lean's maxStrength_precond
spec fn max_strength_precond(nums: Seq<i64>) -> bool {
    nums.len() > 0
}

// Postcondition predicate - equivalent to Lean's maxStrength_postcond  
spec fn max_strength_postcond(nums: Seq<i64>, result: i64) -> bool {
    nums.len() > 0 &&
    exists|i: int| 0 <= i < nums.len() && nums[i] == result &&
    forall|j: int| 0 <= j < nums.len() ==> nums[j] <= result
}

// Main function - equivalent to Lean's maxStrength
fn max_strength(nums: Vec<i64>) -> (result: i64)
    requires max_strength_precond(nums@) // Precondition
    ensures max_strength_postcond(nums@, result) // Postcondition
{
    let mut max_val = nums[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to satisfy termination requirement */
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            exists|k: int| 0 <= k < i && nums@[k] == max_val,
            forall|j: int| 0 <= j < i ==> nums@[j] <= max_val
        decreases nums.len() - i
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }
    
    max_val
}

fn main() {
    let test_vec = vec![1, 5, 3, 9, 2];
    let result = max_strength(test_vec);
    /* code modified by LLM (iteration 1): removed println! as it's not supported in Verus verification */
    // println!("Maximum strength: {}", result);
}

}