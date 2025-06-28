use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Vec<int>, target: int) -> (index1: int, index2: int)
    requires
        2 <= nums.len(),
        exists|i: int, j: int| (0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target)
    ensures
        index1 != index2,
        0 <= index1 < nums.len(),
        0 <= index2 < nums.len(),
        nums.spec_index(index1) + nums.spec_index(index2) == target
{
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            exists|a: int, b: int| (0 <= a < b < nums.len() && nums.spec_index(a) + nums.spec_index(b) == target),
            forall|k1: int, k2: int| (0 <= k1 < i && k1 < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                exists|a: int, b: int| (0 <= a < b < nums.len() && nums.spec_index(a) + nums.spec_index(b) == target),
                forall|k1: int, k2: int| (0 <= k1 < i && k1 < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target,
                forall|k: int| (i + 1 <= k < j) ==> nums.spec_index(i as int) + nums.spec_index(k) != target
        {
            if nums.spec_index(i as int) + nums.spec_index(j as int) == target {
                assert(i as int != j as int);
                assert(0 <= i as int < nums.len());
                assert(0 <= j as int < nums.len());
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // Prove this is unreachable
    proof {
        // From precondition, we know there exists i, j such that nums[i] + nums[j] == target
        // and 0 <= i < j < nums.len()
        let ghost_witness_i = choose|i: int| exists|j: int| (0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target);
        let ghost_witness_j = choose|j: int| (ghost_witness_i < j < nums.len() && nums.spec_index(ghost_witness_i) + nums.spec_index(j) == target);
        
        // The outer loop went through all i from 0 to nums.len()-1
        // So it must have considered i = ghost_witness_i
        assert(0 <= ghost_witness_i < nums.len());
        
        // When i was ghost_witness_i, the inner loop went through all j from ghost_witness_i+1 to nums.len()-1
        // So it must have considered j = ghost_witness_j
        assert(ghost_witness_i < ghost_witness_j < nums.len());
        assert(ghost_witness_i + 1 <= ghost_witness_j);
        
        // But we know nums[ghost_witness_i] + nums[ghost_witness_j] == target
        // So the condition should have been true and we should have returned
        assert(nums.spec_index(ghost_witness_i) + nums.spec_index(ghost_witness_j) == target);
        
        // This contradicts reaching this point
        assert(false);
    }
    
    unreachable()
}

}