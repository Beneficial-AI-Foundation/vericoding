use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Vec<int>, target: int) -> (result: (int, int))
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target
    ensures
        0 <= result.0 < result.1 < nums.len() && nums.spec_index(result.0) + nums.spec_index(result.1) == target,
        forall|ii: int, jj: int| (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
        forall|jj: int| result.0 < jj < result.1 ==> nums.spec_index(result.0) + nums.spec_index(jj) != target
{
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            0 <= i < nums.len(),
            forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
            exists|x: int, y: int| (i as int) <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len() - 1,
                i + 1 <= j <= nums.len(),
                forall|jj: int| (i as int) + 1 <= jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target,
                forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
                exists|x: int, y: int| (i as int) <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target
        {
            if nums[i] + nums[j] == target {
                // Add proof that this satisfies all postconditions
                assert(0 <= i < j < nums.len());
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                
                // Prove the first postcondition about no earlier solutions
                assert(forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
                
                // Prove the second postcondition about no solutions between i and j
                assert(forall|jj: int| (i as int) < jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target) by {
                    // This follows from the inner loop invariant
                };
                
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // This should never be reached due to precondition
    proof {
        // The precondition guarantees a solution exists, and our loops cover all pairs
        // Since we didn't return, we have a contradiction
        assert(false) by {
            // By the precondition, there exists i, j such that nums[i] + nums[j] == target
            // Our nested loops check all pairs (i, j) with 0 <= i < j < nums.len()
            // If we reach here, we checked all such pairs and found none equal to target
            // This contradicts the precondition
        };
    }
    (0, 1) // unreachable
}

}