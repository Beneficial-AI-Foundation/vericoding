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
            nums.len() > 1,
            forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
            exists|x: int, y: int| (i as int) <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len() - 1,
                i + 1 <= j <= nums.len(),
                nums.len() > 1,
                forall|jj: int| (i as int) + 1 <= jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target,
                forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
                exists|x: int, y: int| (i as int) <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target
        {
            if nums.index(i) + nums.index(j) == target {
                assert(nums.spec_index(i as int) == nums.index(i));
                assert(nums.spec_index(j as int) == nums.index(j));
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= (i as int) < (j as int) < nums.len());
                
                // Prove the second postcondition
                assert(forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
                
                // Prove the third postcondition
                assert(forall|jj: int| (i as int) < jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target);
                
                return (i as int, j as int);
            }
            j += 1;
        }
        
        // After inner loop, we know no solution exists with current i
        assert(forall|jj: int| (i as int) + 1 <= jj < nums.len() ==> nums.spec_index(i as int) + nums.spec_index(jj) != target);
        
        // But we still have the existence guarantee for remaining indices
        assert(exists|x: int, y: int| (i as int) <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target);
        
        // Since no solution with x = i, the solution must have x > i
        assert(exists|x: int, y: int| (i as int) + 1 <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target);
        
        i += 1;
    }
    
    // This point should never be reached due to precondition
    // The existence precondition guarantees a solution exists, but our loop should have found it
    assert(exists|x: int, y: int| 0 <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target);
    assert(forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
    assert(i as int >= nums.len() - 1);
    
    // This creates a contradiction: we have a solution that exists, but we've checked all valid pairs
    assert(false);
    (0, 1)
}

}