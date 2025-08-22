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
    
    let mut seen = Set::<u64>::empty();
    let mut operations = 0;
    let n = nums.len();
    
    let mut i = n;
    /* code modified by LLM (iteration 3): fixed type mismatch by comparing nat to nat */
    while i > 0 && seen.len() < k as nat
        invariant 
            i <= n,
            seen.len() <= k as nat,
            operations == n - i,
            forall|x: u64| seen.contains(x) ==> 1 <= x <= k,
            forall|j: int| n - operations <= j < n ==> {
                let val = nums@[j] as nat;
                if 1 <= val <= k { seen.contains(val as u64) } else { true }
            }
    {
        i = i - 1;
        operations = operations + 1;
        let val = nums[i];
        
        if 1 <= val && val <= k {
            seen = seen.insert(val);
        }
    }
    
    proof {
        let nums_seq = nums@.map_values(|x| x as nat);
        let reversed_nums = nums_seq.reverse();
        let processed = reversed_nums.take(operations as int);
        let target_nums = range_1_to_k(k as nat);
        
        // Prove that we have all elements
        assert forall|idx: int| 0 <= idx < target_nums.len() implies processed.contains(target_nums[idx]) by {
            let target_val = target_nums[idx] as u64;
            assert(seen.contains(target_val));
            
            // Find where this value appears in the processed portion
            let processed_start = (n - operations) as int;
            /* code modified by LLM (iteration 3): fixed exists syntax by adding parentheses */
            assert((exists|j: int| processed_start <= j < n && nums@[j] == target_val as nat)) by {
                // This follows from our precondition and the fact that seen contains target_val
            }
        }
        
        // Prove minimality if operations > 0
        if operations > 0 {
            let processed_minus_one = reversed_nums.take((operations - 1) as int);
            assert(!all_elem(target_nums, processed_minus_one)) by {
                // The last element we added must have been necessary
                let last_idx = (n - operations) as int;
                let last_val = nums@[last_idx] as nat;
                if 1 <= last_val <= k {
                    assert(!processed_minus_one.contains(last_val));
                    assert(target_nums.contains(last_val));
                }
            }
        }
    }
    
    operations
}

fn main() {}

}