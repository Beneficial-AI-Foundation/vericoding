use vstd::prelude::*;

verus! {

// Precondition: there's exactly one pair that sums to target  
spec fn two_sum_precond(nums: Seq<i32>, target: i32) -> bool {
    nums.len() > 1 && 
    exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target &&
    forall|i1: int, j1: int, i2: int, j2: int| 
        (0 <= i1 < j1 < nums.len() && nums[i1] + nums[j1] == target &&
         0 <= i2 < j2 < nums.len() && nums[i2] + nums[j2] == target) ==> 
        (i1 == i2 && j1 == j2)
}

// Helper function to find complement
fn find_complement(nums: &Vec<i32>, target: i32, i: usize, x: i32) -> (result: Option<usize>)
    requires 
        i < nums.len(),
        nums[i as int] == x,
    ensures
        match result {
            Some(j) => {
                let j_int = j as int;
                let i_int = i as int;
                i < j && j < nums.len() && x + nums[j_int] == target
            },
            None => forall|j: int| i < j < nums.len() ==> x + nums[j] != target,
        },
{
    let mut j = i + 1;
    while j < nums.len()
        invariant 
            i < nums.len(),
            i + 1 <= j <= nums.len(),
            nums[i as int] == x,
            forall|k: int| i < k < j ==> x + nums[k] != target,
        decreases nums.len() - j,
    {
        // Check for arithmetic overflow before addition
        let sum_result = x.checked_add(nums[j]);
        if let Some(sum) = sum_result {
            if sum == target {
                return Some(j);
            }
        }
        j += 1;
    }
    None
}

// Main auxiliary function that searches from a given starting index
fn two_sum_aux(nums: &Vec<i32>, target: i32, start_i: usize) -> (result: Option<(usize, usize)>)
    requires 
        nums.len() > 1,
        start_i <= nums.len(),
    ensures
        match result {
            Some((i, j)) => {
                let i_int = i as int;
                let j_int = j as int;
                i >= start_i && i < j && j < nums.len() && 
                nums[i_int] + nums[j_int] == target
            },
            None => forall|i: int, j: int| start_i <= i < j < nums.len() ==> nums[i] + nums[j] != target,
        },
    decreases nums.len() - start_i
{
    if start_i >= nums.len() {
        return None;
    }
    
    let mut i = start_i;
    while i < nums.len()
        invariant 
            start_i <= i <= nums.len(),
            nums.len() > 1,
            forall|k: int, l: int| start_i <= k < i && k < l < nums.len() ==> nums[k] + nums[l] != target,
        decreases nums.len() - i,
    {
        if let Some(j) = find_complement(nums, target, i, nums[i]) {
            return Some((i, j));
        }
        i += 1;
    }
    None
}

// Main function
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires 
        two_sum_precond(nums@, target),
    ensures
        two_sum_postcond(nums@, target, result),
{
    let solution = two_sum_aux(nums, target, 0);
    match solution {
        Some(pair) => {
            proof {
                let (i, j) = pair;
                let i_int = i as int;
                let j_int = j as int;
                assert(i < j && j < nums.len() && nums@[i_int] + nums@[j_int] == target);
            }
            pair
        },
        None => {
            // This should never happen if precondition holds
            proof { 
                // The precondition guarantees existence of a solution, 
                // but aux function found none - contradiction
                let nums_seq = nums@;
                assert(exists|i: int, j: int| 0 <= i < j < nums_seq.len() && nums_seq[i] + nums_seq[j] == target);
                assert(forall|i: int, j: int| 0 <= i < j < nums_seq.len() ==> nums_seq[i] + nums_seq[j] != target);
                assert(false);
            }
            (0, 0) // unreachable
        }
    }
}

// Postcondition
spec fn two_sum_postcond(nums: Seq<i32>, target: i32, result: (usize, usize)) -> bool {
    let (i, j) = result;
    let i_int = i as int;
    let j_int = j as int;
    i < j &&
    i_int < nums.len() &&
    j_int < nums.len() &&
    nums[i_int] + nums[j_int] == target
}

// Theorem stating the specification is satisfied
proof fn two_sum_spec_satisfied(nums: &Vec<i32>, target: i32) 
    requires two_sum_precond(nums@, target),
    ensures {
        let result = two_sum(nums, target);
        two_sum_postcond(nums@, target, result)
    }
{
    // The proof is automatically handled by the ensures clause of two_sum
}

}

fn main() {}