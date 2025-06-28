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
        
        // Establish bounds for mid
        assert(left < right);
        assert(left <= mid);
        assert(mid < right);
        assert(mid < a.len());
        
        if a[mid as int] < key {
            // Prove that all elements from 0 to mid are < key using sorted property
            assert forall|i: int| 0 <= i <= mid implies a.spec_index(i) < key by {
                if 0 <= i <= mid as int {
                    if i == mid as int {
                        assert(a.spec_index(i) == a.spec_index(mid as int));
                        assert(a.spec_index(mid as int) < key);
                    } else {
                        // i < mid, so by sorted property: a[i] <= a[mid] < key
                        assert(i < mid as int);
                        assert(0 <= i < mid as int);
                        assert(mid < a.len());
                        assert(a.spec_index(i) <= a.spec_index(mid as int));
                        assert(a.spec_index(mid as int) < key);
                    }
                }
            };
            left = mid + 1;
        } else {
            // a[mid] >= key
            // Prove that all elements from mid to end are >= key using sorted property
            assert forall|i: int| mid <= i < a.len() implies a.spec_index(i) >= key by {
                if mid as int <= i < a.len() {
                    if i == mid as int {
                        assert(a.spec_index(i) == a.spec_index(mid as int));
                        assert(a.spec_index(mid as int) >= key);
                    } else {
                        // mid < i, so by sorted property: a[mid] <= a[i] and a[mid] >= key
                        assert(mid as int < i);
                        assert(0 <= mid as int < i < a.len());
                        assert(a.spec_index(mid as int) <= a.spec_index(i));
                        assert(a.spec_index(mid as int) >= key);
                    }
                }
            };
            right = mid;
        }
    }
    
    // At this point: left == right
    assert(left == right);
    
    // Establish postconditions
    let result = left as int;
    
    // The loop invariants directly give us most postconditions
    assert(0 <= result <= a.len());
    assert(forall|i: int| 0 <= i < result ==> a.spec_index(i) < key);
    assert(forall|i: int| result <= i < a.len() ==> a.spec_index(i) >= key);
    
    // Handle the special case when result == a.len()
    if result == a.len() {
        assert forall|i: int| 0 <= i < a.len() implies a.spec_index(i) < key by {
            if 0 <= i < a.len() {
                assert(i < result);
                // This follows from the loop invariant
            }
        };
    }
    
    result
}

}