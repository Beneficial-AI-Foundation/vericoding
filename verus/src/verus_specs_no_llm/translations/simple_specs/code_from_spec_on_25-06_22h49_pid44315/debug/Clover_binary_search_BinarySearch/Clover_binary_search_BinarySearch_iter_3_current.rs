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
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) < key,
        forall|i: int| n <= i < a.len() ==> a.spec_index(i) >= key
{
    let mut left: usize = 0;
    let mut right: usize = a.len();
    
    while left < right
        invariant
            0 <= left <= right <= a.len(),
            forall|i: int| 0 <= i < left ==> a.spec_index(i) < key,
            forall|i: int| right <= i < a.len() ==> a.spec_index(i) >= key
    {
        let mid = left + (right - left) / 2;
        
        assert(left < right);
        assert(left <= mid < right);
        assert(mid < a.len());
        
        if a[mid] < key {
            // Prove that all elements from 0 to mid are < key
            proof {
                // Use the sorted property to establish that all elements <= mid are < key
                assert forall|i: int| 0 <= i <= mid implies a.spec_index(i) < key by {
                    if i <= mid {
                        // By sorted property: a[i] <= a[mid] < key
                        assert(a.spec_index(i) <= a.spec_index(mid as int));
                        assert(a.spec_index(mid as int) < key);
                    }
                }
            }
            left = mid + 1;
        } else {
            // Prove that all elements from mid onwards are >= key
            proof {
                // Use the sorted property to establish that all elements >= mid are >= key
                assert forall|i: int| mid <= i < a.len() implies a.spec_index(i) >= key by {
                    if mid <= i < a.len() {
                        // By sorted property: key <= a[mid] <= a[i]
                        assert(a.spec_index(mid as int) <= a.spec_index(i));
                        assert(a.spec_index(mid as int) >= key);
                    }
                }
            }
            right = mid;
        }
    }
    
    // Final assertions to establish postconditions
    assert(left == right);
    assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < key);
    assert(forall|i: int| left <= i < a.len() ==> a.spec_index(i) >= key);
    
    // Establish the conditional postcondition
    proof {
        if left == a.len() {
            assert forall|i: int| 0 <= i < a.len() implies a.spec_index(i) < key by {
                if 0 <= i < a.len() {
                    assert(i < left);
                }
            }
        }
    }
    
    left as int
}

}