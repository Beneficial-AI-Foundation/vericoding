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
                // Prove the postconditions
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= (i as int) < (j as int) < nums.len());
                
                // Prove that no earlier pairs work
                assert(forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
                
                // Prove that no pairs with i and earlier j work
                assert(forall|jj: int| (i as int) < jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target);
                
                return ((i as int, j as int));
            }
            j += 1;
        }
        i += 1;
    }
    
    // This point should never be reached due to the precondition
    proof {
        // We've exhaustively searched all pairs (ii, jj) where 0 <= ii < nums.len() - 1 and ii < jj < nums.len()
        // But the precondition guarantees such a pair exists with the target sum
        // This is a contradiction
        assert(forall|ii: int, jj: int| (0 <= ii < nums.len() - 1 && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
        
        // From precondition we know there exists such a pair
        let ghost_pair = choose|x: int, y: int| 0 <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target;
        assert(0 <= ghost_pair.0 < ghost_pair.1 < nums.len());
        assert(nums.spec_index(ghost_pair.0) + nums.spec_index(ghost_pair.1) == target);
        
        // Since ghost_pair.0 < ghost_pair.1 and both are valid indices, we must have ghost_pair.0 < nums.len() - 1
        assert(ghost_pair.0 < nums.len() - 1);
        
        // This contradicts our exhaustive search
        assert(false);
    }
    
    unreachable()
}

}