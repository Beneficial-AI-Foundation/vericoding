use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn BinarySearch(a: Vec<int>, key: int) -> (n: int)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    ensures
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a.spec_index(i) < key,
        forall|i: int| n <= i < a.len() ==> key <= a.spec_index(i)
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a.spec_index(i) < key,
            forall|i: int| high <= i < a.len() ==> key <= a.spec_index(i)
    {
        let mid = low + (high - low) / 2;
        
        // Prove that mid is in bounds
        assert(low < high);
        assert(mid >= low);
        assert(mid < high);
        assert(mid < a.len());
        
        if a.spec_index(mid as int) < key {
            low = mid + 1;
            
            // Prove the invariant is maintained for the updated low
            assert(forall|i: int| 0 <= i < (mid + 1) as int ==> a.spec_index(i) < key) by {
                // For all indices from 0 to mid (inclusive), elements are < key
                assert(forall|i: int| 0 <= i < low as int ==> a.spec_index(i) < key); // old invariant
                assert(a.spec_index(mid as int) < key); // from if condition
            };
        } else {
            high = mid;
            
            // Prove the invariant is maintained for the updated high
            assert(forall|i: int| (mid as int) <= i < a.len() ==> key <= a.spec_index(i)) by {
                assert(key <= a.spec_index(mid as int)); // from else condition (not < key)
                assert(forall|i: int| mid as int < i < a.len() ==> key <= a.spec_index(i)) by {
                    // Use sortedness and the fact that key <= a[mid]
                    assert(forall|i: int| mid as int < i < a.len() ==> {
                        a.spec_index(mid as int) <= a.spec_index(i) && // sortedness
                        key <= a.spec_index(mid as int) // from else condition
                    });
                };
            };
        }
    }
    
    low as int
}

}