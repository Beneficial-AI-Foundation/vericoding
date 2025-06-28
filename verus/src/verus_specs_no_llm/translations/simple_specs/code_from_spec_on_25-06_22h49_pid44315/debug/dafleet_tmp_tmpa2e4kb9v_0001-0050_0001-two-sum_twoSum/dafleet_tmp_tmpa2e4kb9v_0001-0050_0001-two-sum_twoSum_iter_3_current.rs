use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    let (i, j) = pair;
    0 <= i < nums.len() && 
    0 <= j < nums.len() && 
    i != j &&
    nums[i] + nums[j] == target
}

fn twoSum(nums: Seq<int>, target: int) -> (pair: (int, int))
    requires
        exists i, j :: correct_pair((i, j), nums, target)
    ensures
        correct_pair(pair, nums, target)
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            exists x, y :: correct_pair((x, y), nums, target),
            forall k1, k2 :: (0 <= k1 < i && 0 <= k2 < nums.len() && k1 != k2) ==> nums[k1] + nums[k2] != target
    {
        let mut j = 0;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                0 <= j <= nums.len(),
                exists x, y :: correct_pair((x, y), nums, target),
                forall k1, k2 :: (0 <= k1 < i && 0 <= k2 < nums.len() && k1 != k2) ==> nums[k1] + nums[k2] != target,
                forall k :: (0 <= k < j && k != i) ==> nums[i] + nums[k] != target
        {
            if i != j && nums[i] + nums[j] == target {
                assert(correct_pair((i, j), nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        
        // After inner loop completes, we know no j works with current i
        assert(forall k :: (0 <= k < nums.len() && k != i) ==> nums[i] + nums[k] != target);
        
        i = i + 1;
    }
    
    // This point should never be reached due to the precondition
    // The precondition guarantees a solution exists, but our loops would have found it
    assert(forall k1, k2 :: (0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 != k2) ==> nums[k1] + nums[k2] != target);
    assert(exists x, y :: correct_pair((x, y), nums, target));
    assert(false); // Contradiction - solution must exist but we didn't find it
    (0, 0)
}

}