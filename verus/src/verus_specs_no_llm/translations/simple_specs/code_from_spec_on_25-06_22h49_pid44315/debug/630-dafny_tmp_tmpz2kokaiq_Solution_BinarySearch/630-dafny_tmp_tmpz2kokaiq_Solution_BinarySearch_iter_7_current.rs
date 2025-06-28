use builtin::*;
use builtin_macros::*;

verus! {

spec fn sorted(a: Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
}

fn main() {
}

fn BinarySearch(a: Vec<int>, x: int) -> (index: int)
    requires
        sorted(a)
    ensures
        0 <= index < a.len() ==> a.spec_index(index) == x,
        index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x
{
    if a.len() == 0 {
        return -1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a.spec_index(i) < x,
            forall|i: int| high <= i < a.len() ==> a.spec_index(i) > x,
            sorted(a)
        decreases high - low
    {
        // Prove that we can safely compute mid without overflow
        assert(low < high);
        assert(high <= a.len());
        
        let mid = low + (high - low) / 2;
        
        // Prove mid is in bounds
        assert(low <= mid < high);
        assert(mid < a.len());
        
        if a[mid] == x {
            // Prove the postcondition holds
            assert(0 <= mid < a.len());
            assert(a.spec_index(mid as int) == x);
            return mid as int;
        } else if a[mid] < x {
            // Update low, maintaining invariant
            assert(forall|i: int| 0 <= i <= mid ==> a.spec_index(i) < x);
            low = mid + 1;
        } else {
            // Update high, maintaining invariant  
            assert(forall|i: int| mid <= i < a.len() ==> a.spec_index(i) > x);
            high = mid;
        }
    }
    
    // When loop exits, low == high, and no element equals x
    assert(low == high);
    assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < x);
    assert(forall|i: int| high <= i < a.len() ==> a.spec_index(i) > x);
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x);
    
    return -1;
}

}