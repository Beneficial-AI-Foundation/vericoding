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
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should be unreachable given the precondition
    // We have an existential guarantee that there exists a valid pair
    assert(exists x, y :: correct_pair((x, y), nums, target));
    
    // But our loop invariant says we've checked all pairs (i, j) where i < nums.len()
    // and found none that work
    assert(forall k1, k2 :: (0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 != k2) ==> nums[k1] + nums[k2] != target);
    
    // This is a direct contradiction - we can't have both:
    // 1. There exists a valid pair (from precondition)  
    // 2. No valid pairs exist (from our exhaustive search)
    assert(false);
    
    (0, 0) // This line is unreachable
}

}