use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn binarySearch(a: Vec<int>, val: int) -> (pos: int)
    requires
        a.len() > 0,
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    ensures
        0 <= pos < a.len() ==> a.spec_index(pos) == val,
        pos < 0 || pos >= a.len() ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val
{
    let mut left: int = 0;
    let mut right: int = (a.len() as int) - 1;
    
    while left <= right
        invariant
            0 <= left <= a.len(),
            -1 <= right < a.len(),
            forall|i: int| 0 <= i < left ==> a.spec_index(i) < val,
            forall|i: int| right < i < a.len() ==> a.spec_index(i) > val
    {
        let mid = left + (right - left) / 2;
        
        // Prove mid is in bounds
        assert(left <= right);
        assert(mid >= left);
        assert(mid <= right);
        assert(0 <= mid < a.len());
        
        if a.spec_index(mid) == val {
            return mid;
        } else if a.spec_index(mid) < val {
            // All elements from left to mid are < val
            assert(forall|i: int| left <= i <= mid ==> a.spec_index(i) <= a.spec_index(mid)) by {
                // Use the sorted property
                assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j));
            };
            assert(forall|i: int| left <= i <= mid ==> a.spec_index(i) < val);
            left = mid + 1;
        } else {
            // All elements from mid to right are > val
            assert(forall|i: int| mid <= i <= right ==> a.spec_index(i) >= a.spec_index(mid)) by {
                // Use the sorted property
                assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j));
            };
            assert(forall|i: int| mid <= i <= right ==> a.spec_index(i) > val);
            right = mid - 1;
        }
    }
    
    // When we exit the loop, left > right
    // We need to prove that no element equals val
    assert(left > right);
    
    // The key insight: when left > right, we have:
    // - all elements in [0, left) are < val
    // - all elements in (right, a.len()) are > val  
    // - since left > right, we have left >= right + 1
    // - this means [0, left) and (right, a.len()) cover all indices
    
    assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right)) by {
        // Since left > right, either i < left or i > right for any valid i
        assert(left > right);
    };
    
    // Therefore no element can equal val
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val) by {
        assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < val);
        assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > val);
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right));
    };
    
    return -1;
}

}