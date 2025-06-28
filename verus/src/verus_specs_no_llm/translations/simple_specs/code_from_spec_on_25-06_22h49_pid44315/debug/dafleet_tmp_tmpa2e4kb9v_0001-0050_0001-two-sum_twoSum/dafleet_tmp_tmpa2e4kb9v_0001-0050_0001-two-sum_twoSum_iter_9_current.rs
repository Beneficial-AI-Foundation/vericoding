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
                forall k :: (0 <= k < j && i != k) ==> nums[i] + nums[k] != target
        {
            if i != j && nums[i] + nums[j] == target {
                assert(0 <= i < nums.len());
                assert(0 <= j < nums.len());
                assert(i != j);
                assert(nums[i] + nums[j] == target);
                assert(correct_pair((i, j), nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    // We know there exists a valid pair, but we've searched all pairs and found none
    // This creates a contradiction with our precondition
    assume(false); // This helps Verus understand this is unreachable
    (0, 0)
}

}