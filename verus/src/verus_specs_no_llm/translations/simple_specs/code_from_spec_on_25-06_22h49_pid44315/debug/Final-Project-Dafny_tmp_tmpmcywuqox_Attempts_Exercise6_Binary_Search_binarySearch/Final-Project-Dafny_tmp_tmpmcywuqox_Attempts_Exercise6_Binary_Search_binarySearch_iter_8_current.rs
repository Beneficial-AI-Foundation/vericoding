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
        (0 <= pos < a.len()) ==> a.spec_index(pos) == val,
        (pos == -1) ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val,
        pos == -1 || (0 <= pos < a.len())
{
    let mut left: int = 0;
    let mut right: int = (a.len() as int) - 1;
    
    while left <= right
        invariant
            0 <= left <= a.len(),
            -1 <= right < a.len(),
            forall|i: int| 0 <= i < left ==> a.spec_index(i) < val,
            forall|i: int| right < i < a.len() ==> a.spec_index(i) > val,
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    {
        let mid = left + (right - left) / 2;
        
        // Prove mid is in bounds
        assert(left <= right);
        assert(0 <= left <= right < a.len());
        assert(left <= mid <= right) by {
            assert((right - left) / 2 >= 0);
            assert((right - left) / 2 <= right - left);
        };
        assert(0 <= mid < a.len());
        
        if a.spec_index(mid) == val {
            return mid;
        } else if a.spec_index(mid) < val {
            // Update invariant: all elements from left to mid are < val
            assert(forall|i: int| left <= i <= mid ==> a.spec_index(i) < val) by {
                // Elements from left to mid-1 are already < val by invariant
                assert(forall|i: int| left <= i < mid ==> a.spec_index(i) < val);
                // mid element is < val by condition
                assert(a.spec_index(mid) < val);
                // Use sorted property to prove elements left to mid are <= mid
                assert(forall|i: int| left <= i < mid ==> a.spec_index(i) <= a.spec_index(mid)) by {
                    assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j));
                };
            };
            left = mid + 1;
        } else {
            // Update invariant: all elements from mid to right are > val
            assert(a.spec_index(mid) > val);
            assert(forall|i: int| mid <= i <= right ==> a.spec_index(i) > val) by {
                // Elements from mid+1 to right are already > val by invariant
                assert(forall|i: int| mid < i <= right ==> a.spec_index(i) > val);
                // mid element is > val by condition
                assert(a.spec_index(mid) > val);
                // Use sorted property to prove elements right of mid are >= mid
                assert(forall|i: int| mid < i <= right ==> a.spec_index(mid) <= a.spec_index(i)) by {
                    assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j));
                };
            };
            right = mid - 1;
        }
    }
    
    // When we exit the loop, left > right
    assert(left > right);
    
    // Prove that val is not in the array
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val) by {
        // By invariants: elements [0, left) are < val and elements (right, len) are > val
        assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < val);
        assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > val);
        
        // Since left > right, every valid index is either < left or > right
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right)) by {
            // If left > right and both are within bounds, there's no gap
            assert(left > right);
            assert(0 <= left <= a.len());
            assert(-1 <= right < a.len());
        };
    };
    
    return -1;
}

}