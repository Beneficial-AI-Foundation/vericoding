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
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid < high);
        assert(0 <= mid < a.len());
        
        if a[mid] == x {
            assert(a.spec_index(mid as int) == x);
            return mid as int;
        } else if a[mid] < x {
            // Since array is sorted and a[mid] < x, all elements from 0 to mid are < x
            assert(forall|i: int| 0 <= i <= mid ==> a.spec_index(i) < x) by {
                // Elements from 0 to low-1 are already < x by invariant
                assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < x);
                
                // For elements from low to mid, use sortedness
                forall|i: int| low <= i <= mid implies a.spec_index(i) < x by {
                    if low <= i <= mid {
                        // By sortedness: a[i] <= a[mid]
                        assert(a.spec_index(i) <= a.spec_index(mid as int));
                        // We know a[mid] < x
                        assert(a.spec_index(mid as int) < x);
                        // Therefore a[i] < x
                        assert(a.spec_index(i) < x);
                    }
                }
            };
            low = mid + 1;
        } else {
            // Since array is sorted and a[mid] > x, all elements from mid to end are > x
            assert(forall|i: int| mid <= i < a.len() ==> a.spec_index(i) > x) by {
                // Elements from high to end are already > x by invariant
                assert(forall|i: int| high <= i < a.len() ==> a.spec_index(i) > x);
                
                // For elements from mid to high-1, use sortedness
                forall|i: int| mid <= i < high implies a.spec_index(i) > x by {
                    if mid <= i < high {
                        // By sortedness: a[mid] <= a[i]
                        assert(a.spec_index(mid as int) <= a.spec_index(i));
                        // We know a[mid] > x
                        assert(a.spec_index(mid as int) > x);
                        // Therefore a[i] > x
                        assert(a.spec_index(i) > x);
                    }
                }
            };
            high = mid;
        }
    }
    
    // At this point low == high, prove no element equals x
    assert(low == high);
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x) by {
        forall|i: int| 0 <= i < a.len() implies a.spec_index(i) != x by {
            if 0 <= i < a.len() {
                if i < low {
                    // From invariant: a[i] < x
                    assert(a.spec_index(i) < x);
                    assert(a.spec_index(i) != x);
                } else {
                    // Since low == high and i >= low, we have i >= high
                    assert(i >= high);
                    // From invariant: a[i] > x
                    assert(a.spec_index(i) > x);
                    assert(a.spec_index(i) != x);
                }
            }
        }
    };
    
    return -1;
}

}