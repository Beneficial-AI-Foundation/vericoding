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
        let mid = low + (high - low) / 2;
        
        if a[mid] == x {
            return mid as int;
        } else if a[mid] < x {
            // All elements from 0 to mid are < x, so we can safely move low to mid + 1
            proof {
                assert(a.spec_index(mid as int) < x);
                // Use sortedness to prove that all elements <= mid are < x
                assert(forall|i: int| 0 <= i <= mid ==> a.spec_index(i) <= a.spec_index(mid as int) < x);
            }
            low = mid + 1;
        } else {
            // a[mid] > x, so all elements from mid onwards are > x
            proof {
                assert(a.spec_index(mid as int) > x);
                // Use sortedness to prove that all elements >= mid are > x
                assert(forall|i: int| mid <= i < a.len() ==> a.spec_index(mid as int) <= a.spec_index(i));
                assert(forall|i: int| mid <= i < a.len() ==> x < a.spec_index(mid as int) <= a.spec_index(i));
            }
            high = mid;
        }
    }
    
    // When loop exits, low == high
    // The invariants tell us that all elements < low are < x and all elements >= high are > x
    // Since low == high, we've covered the entire array and found no element equal to x
    proof {
        assert(low == high);
        assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < x);
        assert(forall|i: int| high <= i < a.len() ==> a.spec_index(i) > x);
        // Since low == high, every index is either < low or >= high
        assert(forall|i: int| 0 <= i < a.len() ==> (i < low || i >= high));
        assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x);
    }
    
    return -1;
}

}