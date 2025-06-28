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
        assert(left <= mid < right);
        assert(mid < a.len());
        
        if a[mid] < key {
            // Prove that all elements from left to mid (inclusive) are < key
            assert forall|i: int| left <= i <= mid as int implies a.spec_index(i) < key by {
                if left <= i <= mid as int {
                    if i < mid as int {
                        // By sorted property: a[i] <= a[mid] and a[mid] < key
                        assert(a.spec_index(i) <= a.spec_index(mid as int));
                    } else {
                        // i == mid
                        assert(i == mid as int);
                    }
                }
            };
            left = mid + 1;
        } else {
            // a[mid] >= key
            // Prove that all elements from mid onwards are >= key
            assert forall|i: int| mid as int <= i < a.len() implies a.spec_index(i) >= key by {
                if mid as int <= i < a.len() {
                    // By sorted property: a[mid] <= a[i] and a[mid] >= key
                    assert(a.spec_index(mid as int) <= a.spec_index(i));
                }
            };
            right = mid;
        }
    }
    
    let result = left as int;
    
    // Final verification that postconditions hold
    assert(left == right);
    assert(0 <= result <= a.len());
    
    // These follow from the loop invariants
    assert(forall|i: int| 0 <= i < result ==> a.spec_index(i) < key);
    assert(forall|i: int| result <= i < a.len() ==> a.spec_index(i) >= key);
    
    // The third postcondition is a special case
    if result == a.len() {
        assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) < key);
    }
    
    result
}

}