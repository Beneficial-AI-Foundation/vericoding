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
        // Calculate mid more carefully
        let mid = left + (right - left) / 2;
        
        // Prove mid is in bounds
        assert(0 <= mid < a.len()) by {
            // Since left <= right and both are valid indices
            assert(left <= right);
            assert(0 <= left);
            assert(right < a.len());
            
            // mid >= left since (right - left) / 2 >= 0
            assert(mid >= left) by {
                assert((right - left) / 2 >= 0);
                assert(mid == left + (right - left) / 2);
            };
            
            // mid <= right since (right - left) / 2 <= (right - left)
            assert(mid <= right) by {
                assert((right - left) / 2 <= right - left);
                assert(mid == left + (right - left) / 2);
                assert(left + (right - left) / 2 <= left + (right - left));
                assert(left + (right - left) == right);
            };
            
            // Therefore 0 <= left <= mid <= right < a.len()
            assert(0 <= mid);
            assert(mid < a.len());
        };
        
        if a.spec_index(mid) == val {
            return mid;
        } else if a.spec_index(mid) < val {
            left = mid + 1;
            
            // Prove the invariant is maintained
            assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < val) by {
                assert(forall|i: int| 0 <= i < mid + 1 ==> a.spec_index(i) < val) by {
                    // For i < mid, this follows from the old invariant
                    // For i == mid, we know a.spec_index(mid) < val from the condition
                    assert(a.spec_index(mid) < val);
                };
            };
        } else {
            assert(a.spec_index(mid) > val);
            right = mid - 1;
            
            // Prove the invariant is maintained
            assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > val) by {
                assert(forall|i: int| mid - 1 < i < a.len() ==> a.spec_index(i) > val) by {
                    // For i > mid, this follows from the old invariant
                    // For i == mid, we know a.spec_index(mid) > val from the condition
                    assert(a.spec_index(mid) > val);
                };
            };
        }
    }
    
    // When we exit the loop, left > right
    // The invariants guarantee that val is not in the array
    assert(left > right);
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val) by {
        // At this point, left > right
        // The invariants tell us:
        // - forall i < left: a[i] < val
        // - forall i > right: a[i] > val  
        // Since left > right, we cover all indices 0..a.len()
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right)) by {
            assert(left > right);
        };
    };
    
    return -1;
}

}