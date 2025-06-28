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
        
        if a[mid] < key {
            low = mid + 1;
            // Prove loop invariant: all elements before new low are < key
            assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < key) by {
                assert(forall|i: int| 0 <= i < mid + 1 ==> a.spec_index(i) < key) by {
                    // For any i in range [0, mid + 1)
                    assert(forall|i: int| 0 <= i < mid + 1 ==> {
                        if i < (mid as int) {
                            // Elements before mid are < key by loop invariant
                            a.spec_index(i) < key
                        } else {
                            // i == mid, and a[mid] < key by condition
                            i == mid && a.spec_index(i) < key
                        }
                    });
                };
            };
        } else {
            high = mid;
            // Prove loop invariant: all elements from new high are >= key
            assert(forall|i: int| high <= i < a.len() ==> key <= a.spec_index(i)) by {
                assert(forall|i: int| mid <= i < a.len() ==> key <= a.spec_index(i)) by {
                    // For any i in range [mid, a.len())
                    assert(forall|i: int| mid <= i < a.len() ==> {
                        if i == mid {
                            // Element at mid is >= key by condition
                            key <= a.spec_index(i)
                        } else {
                            // i > mid, so by sortedness and a[mid] >= key, we have a[i] >= key
                            // Use sortedness: a[mid] <= a[i] and key <= a[mid]
                            key <= a.spec_index(i)
                        }
                    });
                };
            };
        }
    }
    
    low as int
}

}