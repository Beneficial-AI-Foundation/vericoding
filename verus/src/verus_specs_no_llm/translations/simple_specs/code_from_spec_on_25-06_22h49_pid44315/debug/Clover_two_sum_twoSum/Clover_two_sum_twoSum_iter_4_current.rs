use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Vec<int>, target: int) -> (i: int, j: int)
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target
    ensures
        0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target,
        forall|ii: int, jj: int| (0 <= ii < i && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
        forall|jj: int| i < jj < j ==> nums.spec_index(i) + nums.spec_index(jj) != target
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
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= (i as int) < (j as int) < nums.len());
                assert(forall|ii: int, jj: int| (0 <= ii < (i as int) && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
                assert(forall|jj: int| (i as int) < jj < (j as int) ==> nums.spec_index(i as int) + nums.spec_index(jj) != target);
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // This point should never be reached due to the precondition
    proof {
        assert(i == nums.len() - 1);
        assert(forall|ii: int, jj: int| (0 <= ii < nums.len() - 1 && ii < jj < nums.len()) ==> nums.spec_index(ii) + nums.spec_index(jj) != target);
        // We know from precondition that there exists a solution
        assert(exists|x: int, y: int| 0 <= x < y < nums.len() && nums.spec_index(x) + nums.spec_index(y) == target);
        // This contradicts our exhaustive search that found no solution
        assert(false);
    }
    
    // Verus requires explicit unreachable, but we prove it's unreachable above
    unreachable()
}

}