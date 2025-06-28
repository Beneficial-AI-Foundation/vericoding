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
                assert(correct_pair((i, j), nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // At this point, we've checked all pairs where k1 < k2 in the outer loop
    // But we know from the precondition that a valid pair exists
    // The issue is our invariant is too strong - it says no pair with k1 < i works
    // But the existing pair might have k1 >= i
    
    // Since we know a pair exists from precondition, and we've exhausted our search,
    // we need to reconsider our approach. Let's add a proof by contradiction:
    
    proof {
        // We know there exists some valid pair (x, y)
        let (x, y) = choose |x: int, y: int| correct_pair((x, y), nums, target);
        
        // We've checked all pairs, so we should have found it
        // This creates a contradiction, proving this point is unreachable
        assert(false);
    }
    
    (0, 0) // This line is unreachable
}

}