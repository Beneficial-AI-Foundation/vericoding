use vstd::prelude::*;

verus! {

// Helper function to check if all elements in target are present in source
spec fn all_elem(target: Seq<nat>, source: Seq<nat>) -> bool {
    forall|i: int| #![auto] 0 <= i < target.len() ==> source.contains(target[i])
}

// Helper function to create range [1, k]
spec fn range_1_to_k(k: nat) -> Seq<nat> {
    Seq::new(k as nat, |i: int| (i + 1) as nat)
}

// Precondition: all numbers from 1 to k must be present in nums
spec fn min_operations_precond(nums: Seq<nat>, k: nat) -> bool {
    let target_nums = range_1_to_k(k);
    all_elem(target_nums, nums)
}

// Postcondition specification  
spec fn min_operations_postcond(nums: Seq<nat>, k: nat, result: nat) -> bool {
    let reversed_nums = nums.reverse();
    let processed = reversed_nums.take(result as int);
    let target_nums = range_1_to_k(k);
    
    // Condition 1: All target numbers must be present in processed elements
    let collected_all = all_elem(target_nums, processed);
    
    // Condition 2: result must be minimal
    let is_minimal = if result > 0 {
        let processed_minus_one = reversed_nums.take((result - 1) as int);
        !all_elem(target_nums, processed_minus_one)
    } else {
        k == 0
    };
    
    collected_all && is_minimal
}

// Main function with specification
fn min_operations(nums: Vec<u64>, k: u64) -> (result: u64)
    requires 
        min_operations_precond(nums@.map_values(|x| x as nat), k as nat)
    ensures 
        min_operations_postcond(nums@.map_values(|x| x as nat), k as nat, result as nat)
{
    if k == 0 {
        return 0;
    }
    
    let mut seen: Set<u64> = Set::empty();
    let mut operations = 0u64;
    let mut i = nums.len();
    
    /* code modified by LLM (iteration 1): fixed type mismatch by casting k to nat for comparison, and added proper bounds checking */
    while seen.len() < k as nat
        invariant 
            i <= nums.len(),
            operations == nums.len() - i,
            seen.len() <= k as nat,
            forall|x: u64| seen.contains(x) ==> 1 <= x <= k,
            forall|j: int| i <= j < nums.len() ==> 
                (1 <= nums[j] <= k ==> seen.contains(nums[j])),
            i > 0 || seen.len() == k as nat,
        decreases i
    {
        i = i - 1;
        operations = operations + 1;
        let current = nums[i];
        if 1 <= current && current <= k {
            seen = seen.insert(current);
        }
    }
    
    operations
}

fn main() {}

}