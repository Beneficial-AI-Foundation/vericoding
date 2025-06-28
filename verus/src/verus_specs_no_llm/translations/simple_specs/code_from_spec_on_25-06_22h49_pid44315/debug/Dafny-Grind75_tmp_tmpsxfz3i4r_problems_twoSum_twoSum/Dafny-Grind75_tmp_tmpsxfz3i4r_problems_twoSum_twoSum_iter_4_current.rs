use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn summingPair(i: nat, j: nat, nums: Seq<int>, target: int) -> bool
    requires i < nums.len()
    requires j < nums.len()
{
    i != j && nums[i] + nums[j] == target
}

fn twoSum(nums: Seq<int>, target: int) -> (pair: (nat, nat))
    requires
        exists i:nat,j:nat :: i < j < nums.len() && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l < m < nums.len() && (l != i || m != j) ==> !summingPair(l, m, nums, target)
    ensures
        0 <= pair.0 < nums.len() && 0 <= pair.1 < nums.len() && summingPair(pair.0, pair.1, nums, target)
{
    let mut i = 0;
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            exists si:nat,sj:nat :: si < sj < nums.len() && summingPair(si, sj, nums, target),
            forall k: nat, l: nat :: k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant 
                i + 1 <= j <= nums.len(),
                i < nums.len(),
                exists si:nat,sj:nat :: si < sj < nums.len() && summingPair(si, sj, nums, target),
                forall k: nat, l: nat :: k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
                forall l: nat :: i + 1 <= l < j ==> !summingPair(i, l, nums, target),
        {
            if nums[i] + nums[j] == target {
                assert(i < nums.len());
                assert(j < nums.len());
                assert(i != j) by {
                    assert(j >= i + 1);
                }
                assert(summingPair(i, j, nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    // From the precondition, we know there exists a solution
    // But our invariants show we've checked all pairs without finding one
    // This is a contradiction
    assert(false) by {
        // We know from precondition that a solution exists
        assert(exists si:nat,sj:nat :: si < sj < nums.len() && summingPair(si, sj, nums, target));
        
        // But our loop invariant when i == nums.len() tells us we've checked all pairs
        // and found no solution, which is a contradiction
        assert(forall k: nat, l: nat :: k < l < nums.len() && k < nums.len() ==> !summingPair(k, l, nums, target));
    }
    
    (0, 0) // This line is unreachable
}

}