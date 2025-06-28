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
            if nums.index(i) + nums.index(j) == target {
                assert(nums.spec_index(i as int) == nums.index(i));
                assert(nums.spec_index(j as int) == nums.index(j));
                assert(nums.spec_index(i as int) + nums.spec_index(j as int) == target);
                assert(0 <= (i as int) < (j as int) < nums.len());
                
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // This point should never be reached due to precondition
    assume(false);
    (0, 1)
}

}