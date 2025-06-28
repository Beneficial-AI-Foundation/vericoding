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
    // Use choose to extract the witness from the existential
    let ghost si = choose|i:nat| exists|j:nat| i < j < nums.len() && summingPair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && (l != i || m != j) ==> !summingPair(l, m, nums, target);
    let ghost sj = choose|j:nat| si < j < nums.len() && summingPair(si, sj, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && (l != si || m != j) ==> !summingPair(l, m, nums, target);
    
    let mut i = 0;
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            si < sj < nums.len() && summingPair(si, sj, nums, target),
            forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant 
                i + 1 <= j <= nums.len(),
                0 <= i < nums.len(),
                si < sj < nums.len() && summingPair(si, sj, nums, target),
                forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
                forall|l: nat| i + 1 <= l < j ==> !summingPair(i, l, nums, target),
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                assert(i != j);
                assert(summingPair(i, j, nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        
        // After inner loop, we know no pair starting with i works
        // This is important for maintaining the invariant
        assert(forall|l: nat| i + 1 <= l < nums.len() ==> !summingPair(i, l, nums, target));
        
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    proof {
        // We know there exists a solution (si, sj) where si < sj
        assert(si < sj < nums.len() && summingPair(si, sj, nums, target));
        
        // We've exhausted all i values: i == nums.len()
        assert(i == nums.len());
        
        // Since si < nums.len() and we've checked all i values up to nums.len(),
        // we must have found the solution when i == si
        assert(si < nums.len());
        
        // By the outer loop invariant, for all k < i (which includes si), 
        // no valid pair exists starting with k
        assert(forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target));
        
        // Since si < i, this means !summingPair(si, sj, nums, target)
        assert(si < i);
        assert(si < sj < nums.len());
        assert(!summingPair(si, sj, nums, target));
        
        // But we also know summingPair(si, sj, nums, target) is true
        assert(summingPair(si, sj, nums, target));
        
        // Contradiction - this proves the unreachable code
        assert(false);
    }
    
    (0, 0) // This line is unreachable
}

}