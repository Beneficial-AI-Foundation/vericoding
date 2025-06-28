use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Vec<int>, target: int) -> (index1: int, index2: int)
    requires
        2 <= nums.len(),
        exists|i: int, j: int| (0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target)
    ensures
        index1 != index2,
        0 <= index1 < nums.len(),
        0 <= index2 < nums.len(),
        nums.spec_index(index1) + nums.spec_index(index2) == target
{
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            exists|a: int, b: int| (0 <= a < b < nums.len() && nums.spec_index(a) + nums.spec_index(b) == target),
            forall|k1: int, k2: int| (0 <= k1 < i && i < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                exists|a: int, b: int| (0 <= a < b < nums.len() && nums.spec_index(a) + nums.spec_index(b) == target),
                forall|k1: int, k2: int| (0 <= k1 < i && i < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target,
                forall|k: int| (i + 1 <= k < j) ==> nums.spec_index(i as int) + nums.spec_index(k) != target
        {
            if nums.spec_index(i as int) + nums.spec_index(j as int) == target {
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // At this point, we have checked all pairs (k1, k2) where 0 <= k1 < k2 < nums.len()
    // and found none that sum to target, but the precondition guarantees such a pair exists.
    // This is a contradiction, so this point is unreachable.
    
    // We can prove this by showing that we've covered all possible pairs:
    // - The outer loop covers all i from 0 to nums.len()-1
    // - For each i, the inner loop covers all j from i+1 to nums.len()-1
    // - So we've checked all pairs (i,j) where 0 <= i < j < nums.len()
    
    proof {
        // Since we've exited both loops without returning, we have:
        // forall|k1: int, k2: int| (0 <= k1 < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target
        
        // But the precondition gives us:
        // exists|a: int, b: int| (0 <= a < b < nums.len() && nums.spec_index(a) + nums.spec_index(b) == target)
        
        // These are contradictory, so this is unreachable
        assert(false);
    }
    
    (0, 0) // This line will never be reached
}

}