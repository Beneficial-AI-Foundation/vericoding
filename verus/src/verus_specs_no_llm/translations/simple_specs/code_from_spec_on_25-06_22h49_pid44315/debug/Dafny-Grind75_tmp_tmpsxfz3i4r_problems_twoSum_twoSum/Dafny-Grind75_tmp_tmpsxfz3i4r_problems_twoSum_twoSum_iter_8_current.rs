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
        exists|i:nat,j:nat| i < j < nums.len() && summingPair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && (l != i || m != j) ==> !summingPair(l, m, nums, target)
    ensures
        0 <= pair.0 < nums.len() && 0 <= pair.1 < nums.len() && summingPair(pair.0, pair.1, nums, target)
{
    let mut i = 0;
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            exists|si:nat,sj:nat| si < sj < nums.len() && summingPair(si, sj, nums, target),
            forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant 
                i + 1 <= j <= nums.len(),
                0 <= i < nums.len(),
                exists|si:nat,sj:nat| si < sj < nums.len() && summingPair(si, sj, nums, target),
                forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
                forall|l: nat| i < l < j ==> !summingPair(i, l, nums, target),
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                assert(summingPair(i, j, nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        
        // Strengthen the invariant after inner loop
        assert(forall|l: nat| i < l < nums.len() ==> !summingPair(i, l, nums, target));
        
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    proof {
        // From precondition: there exists a unique solution
        assert(exists|si:nat,sj:nat| si < sj < nums.len() && summingPair(si, sj, nums, target));
        
        // We've checked all pairs (k,l) where k < l < nums.len()
        // The outer loop invariant tells us we've checked all pairs where k < i
        // Since i == nums.len(), we've checked all pairs where k < nums.len()
        assert(i == nums.len());
        
        // For any pair (k,l) where k < l < nums.len(), we must have k < nums.len() = i
        // So by the invariant, !summingPair(k, l, nums, target)
        assert(forall|k: nat, l: nat| k < l < nums.len() ==> k < i);
        assert(forall|k: nat, l: nat| k < l < nums.len() ==> !summingPair(k, l, nums, target));
        
        // This contradicts the existence from the precondition
        assert(false);
    }
    
    (0, 0) // This line is unreachable
}

}