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
            // All pairs (x, y) where 0 <= x < y < i have been checked and are distinct
            forall|x, y| 0 <= x < y < i ==> nums.spec_index(x) != nums.spec_index(y)
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                // Maintain outer loop invariant
                forall|x, y| 0 <= x < y < i ==> nums.spec_index(x) != nums.spec_index(y),
                // Current element i is distinct from all checked elements in range [i+1, j)
                forall|k| i + 1 <= k < j ==> nums.spec_index(i) != nums.spec_index(k)
        {
            if nums.spec_index(i) == nums.spec_index(j) {
                // Found duplicate at positions i and j
                assert(!distinct(nums)) by {
                    assert(0 <= i < j < nums.len());
                    assert(nums.spec_index(i) == nums.spec_index(j));
                };
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // No duplicates found - prove all pairs are distinct
    assert(distinct(nums)) by {
        assert(i == nums.len());
        // The outer loop invariant now gives us exactly what we need
        assert(forall|x, y| 0 <= x < y < nums.len() ==> nums.spec_index(x) != nums.spec_index(y));
    };
    
    false
}

}