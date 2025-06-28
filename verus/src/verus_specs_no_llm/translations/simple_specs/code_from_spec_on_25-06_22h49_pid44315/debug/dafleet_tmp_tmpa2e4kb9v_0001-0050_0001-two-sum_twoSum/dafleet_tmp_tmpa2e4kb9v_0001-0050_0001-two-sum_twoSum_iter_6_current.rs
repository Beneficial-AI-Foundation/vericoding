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
            forall k1, k2 :: (0 <= k1 < i && 0 <= k2 <= k1) ==> nums[k1] + nums[k2] != target
    {
        let mut j = 0;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                0 <= j <= nums.len(),
                exists x, y :: correct_pair((x, y), nums, target),
                forall k1, k2 :: (0 <= k1 < i && 0 <= k2 <= k1) ==> nums[k1] + nums[k2] != target,
                forall k :: (0 <= k < j) ==> (i == k || nums[i] + nums[k] != target)
        {
            if i != j && nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should be unreachable given the precondition
    // We need to derive a contradiction from our invariants
    assert(forall k1, k2 :: (0 <= k1 < nums.len() && 0 <= k2 <= k1) ==> nums[k1] + nums[k2] != target);
    assert(exists x, y :: correct_pair((x, y), nums, target));
    
    // Get the witnesses from the existential
    let ghost_pair = choose|x: int, y: int| correct_pair((x, y), nums, target);
    let (ghost_i, ghost_j) = ghost_pair;
    
    // From correct_pair definition
    assert(0 <= ghost_i < nums.len());
    assert(0 <= ghost_j < nums.len());
    assert(ghost_i != ghost_j);
    assert(nums[ghost_i] + nums[ghost_j] == target);
    
    // Without loss of generality, we can assume ghost_i > ghost_j
    // If ghost_i <= ghost_j, then we have a contradiction with our invariant
    if ghost_i <= ghost_j {
        assert(nums[ghost_i] + nums[ghost_j] != target); // From invariant
        assert(false); // Contradiction
    }
    
    // If ghost_i > ghost_j, then we should have found this pair
    // This is also a contradiction since we exhaustively searched
    assert(false);
    (0, 0)
}

}