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
            left <= right + 1,
            forall|i: int| 0 <= i < left ==> a.spec_index(i) < val,
            forall|i: int| right < i < a.len() ==> a.spec_index(i) > val,
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    {
        let mid = left + (right - left) / 2;
        
        // Prove mid is in bounds
        assert(left <= right);
        assert(left <= mid <= right);
        assert(0 <= mid < a.len());
        
        if a.spec_index(mid) == val {
            return mid;
        } else if a.spec_index(mid) < val {
            // All elements from left to mid are < val
            assert(forall|i: int| left <= i <= mid ==> a.spec_index(i) < val) by {
                let sorted = forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j);
                assert(sorted);
                assert(a.spec_index(mid) < val);
                assert(forall|i: int| left <= i <= mid ==> {
                    if i <= mid {
                        a.spec_index(i) <= a.spec_index(mid)
                    } else {
                        true
                    }
                }) by {
                    assert(forall|i: int| left <= i <= mid ==> (0 <= i < a.len() && 0 <= mid < a.len()));
                    assert(forall|i: int| left <= i <= mid ==> i <= mid);
                    assert(forall|i: int| left <= i <= mid ==> a.spec_index(i) <= a.spec_index(mid)) by {
                        assert(sorted);
                    };
                };
                assert(forall|i: int| left <= i <= mid ==> a.spec_index(i) < val);
            };
            left = mid + 1;
        } else {
            // All elements from mid to right are > val
            assert(forall|i: int| mid <= i <= right ==> a.spec_index(i) > val) by {
                let sorted = forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j);
                assert(sorted);
                assert(a.spec_index(mid) > val);
                assert(forall|i: int| mid <= i <= right ==> a.spec_index(i) >= a.spec_index(mid)) by {
                    assert(forall|i: int| mid <= i <= right ==> (0 <= mid < a.len() && 0 <= i < a.len()));
                    assert(forall|i: int| mid <= i <= right ==> mid <= i);
                    assert(sorted);
                };
                assert(forall|i: int| mid <= i <= right ==> a.spec_index(i) > val);
            };
            right = mid - 1;
        }
    }
    
    // When we exit the loop, left > right
    assert(left > right);
    
    // Prove that all elements are either < val or > val
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val) by {
        assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < val);
        assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > val);
        assert(left > right);
        
        // Every index is either < left or > right
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right)) by {
            assert(left > right);
            assert(0 <= left <= a.len());
            assert(-1 <= right < a.len());
        };
        
        // Therefore every element is either < val or > val
        assert(forall|i: int| 0 <= i < a.len() ==> (a.spec_index(i) < val || a.spec_index(i) > val));
        assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val);
    };
    
    return -1;
}

}