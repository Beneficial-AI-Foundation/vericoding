use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn distinct(nums: Seq<int>) -> bool {
    forall|i, j| 0 <= i < j < nums.len() ==> nums.spec_index(i) != nums.spec_index(j)
}

fn contains_duplicate(nums: Seq<int>) -> (result: bool)
    requires
        1 <= nums.len() <= 100000,
        forall|i| 0 <= i < nums.len() ==> -1000000000 <= nums.spec_index(i) <= 1000000000
    ensures
        result <==> !distinct(nums)
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            // All pairs (x, y) where x < y and both x, y < i are distinct
            forall|x, y| 0 <= x < y < i ==> nums.spec_index(x) != nums.spec_index(y),
            // For all x < i, nums[x] is distinct from all nums[y] where y >= i
            forall|x, y| 0 <= x < i && i <= y < nums.len() ==> nums.spec_index(x) != nums.spec_index(y)
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                // Maintain outer loop invariants
                forall|x, y| 0 <= x < y < i ==> nums.spec_index(x) != nums.spec_index(y),
                forall|x, y| 0 <= x < i && i <= y < nums.len() ==> nums.spec_index(x) != nums.spec_index(y),
                // Current element i is distinct from all checked elements in range [i+1, j)
                forall|k| i + 1 <= k < j ==> nums.spec_index(i) != nums.spec_index(k)
        {
            if nums.spec_index(i) == nums.spec_index(j) {
                // Found duplicate at positions i and j
                assert(!distinct(nums)) by {
                    assert(0 <= i < j < nums.len());
                    assert(nums.spec_index(i) == nums.spec_index(j));
                    // This directly contradicts the distinct property
                };
                return true;
            }
            j = j + 1;
        }
        
        // After inner loop completes, we know nums[i] is distinct from all nums[k] where k > i
        assert(forall|k| i < k < nums.len() ==> nums.spec_index(i) != nums.spec_index(k));
        
        i = i + 1;
    }
    
    // No duplicates found - prove all pairs are distinct
    assert(distinct(nums)) by {
        // At this point i == nums.len(), so the invariants tell us:
        // 1. forall x, y where 0 <= x < y < nums.len(): nums[x] != nums[y] (from first invariant with i = nums.len())
        // 2. The second invariant is vacuous since there's no y >= nums.len()
        assert(forall|x, y| 0 <= x < y < nums.len() ==> nums.spec_index(x) != nums.spec_index(y));
    };
    
    false
}

}