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
            forall|i: int| right < i < a.len() ==> a.spec_index(i) > val
    {
        let mid = left + (right - left) / 2;
        
        assert(left <= mid <= right);
        assert(0 <= mid < a.len());
        
        if a.spec_index(mid) == val {
            assert(0 <= mid < a.len());
            assert(a.spec_index(mid) == val);
            return mid;
        } else if a.spec_index(mid) < val {
            left = mid + 1;
            assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < val);
        } else {
            right = mid - 1;
            assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > val);
        }
    }
    
    // When we exit the loop, left > right
    assert(left > right);
    assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < val);
    assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > val);
    // Since left > right, we have covered all indices 0..a.len()
    assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right));
    assert(forall|i: int| 0 <= i < a.len() ==> (a.spec_index(i) < val || a.spec_index(i) > val));
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != val);
    
    return -1;
}

}