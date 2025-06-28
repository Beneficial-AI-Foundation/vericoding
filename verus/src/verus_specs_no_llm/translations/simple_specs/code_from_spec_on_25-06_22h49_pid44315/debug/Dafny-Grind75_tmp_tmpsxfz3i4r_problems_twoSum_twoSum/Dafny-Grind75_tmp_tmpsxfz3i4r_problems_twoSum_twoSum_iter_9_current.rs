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
    let ghost solution_exists = choose|si:nat,sj:nat| si < sj < nums.len() && summingPair(si, sj, nums, target);
    let ghost si = solution_exists.0;
    let ghost sj = solution_exists.1;
    
    let mut i = 0;
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            si < sj < nums.len() && summingPair(si, sj, nums, target),
            forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
            i <= si ==> si < nums.len() && sj < nums.len(),
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant 
                i + 1 <= j <= nums.len(),
                0 <= i < nums.len(),
                si < sj < nums.len() && summingPair(si, sj, nums, target),
                forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target),
                forall|l: nat| i < l < j ==> !summingPair(i, l, nums, target),
                i <= si ==> si < nums.len() && sj < nums.len(),
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                assert(summingPair(i, j, nums, target));
                return (i, j);
            }
            j = j + 1;
        }
        
        // After inner loop, we know no pair starting with i works
        assert(forall|l: nat| i < l < nums.len() ==> !summingPair(i, l, nums, target));
        
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    proof {
        // We know there exists a solution (si, sj) where si < sj
        assert(si < sj < nums.len() && summingPair(si, sj, nums, target));
        
        // We've exhausted all i values: i == nums.len()
        assert(i == nums.len());
        
        // Since si < nums.len() and we've checked all i values up to nums.len(),
        // we must have checked i = si at some point
        assert(si < nums.len());
        assert(si < i);
        
        // By the loop invariant, we know that for all pairs (k,l) where k < l and k < i,
        // summingPair(k,l) is false
        assert(forall|k: nat, l: nat| k < l < nums.len() && k < i ==> !summingPair(k, l, nums, target));
        
        // Since si < i and si < sj < nums.len(), we have !summingPair(si, sj, nums, target)
        assert(si < i && si < sj < nums.len());
        assert(!summingPair(si, sj, nums, target));
        
        // But we also know summingPair(si, sj, nums, target) is true from our ghost variable
        assert(summingPair(si, sj, nums, target));
        
        // Contradiction
        assert(false);
    }
    
    (0, 0) // This line is unreachable
}

}