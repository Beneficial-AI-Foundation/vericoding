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
        assert(0 <= left <= a.len());
        assert(-1 <= right < a.len());
        assert(left <= right < a.len());
        assert(0 <= mid < a.len()) by {
            assert(left <= mid) by {
                assert((right - left) / 2 >= 0);
            };
            assert(mid <= right) by {
                assert((right - left) / 2 <= right - left);
            };
        };
        
        if a.spec_index(mid) == val {
            return mid;
        } else if a.spec_index(mid) < val {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }
    
    // When we exit the loop, left > right
    // The invariants guarantee that val is not in the array
    return -1;
}

}