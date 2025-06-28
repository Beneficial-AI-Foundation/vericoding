use builtin::*;
use builtin_macros::*;

verus! {

spec fn isSorted(a: Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
}

fn main() {
}

fn binSearch(a: Vec<int>, K: int) -> (b: bool)
    requires
        isSorted(a)
    ensures
        b == exists|i: nat| i < a.len() && a.spec_index(i) == K
{
    if a.len() == 0 {
        return false;
    }
    
    let mut low: usize = 0;
    let mut high: usize = a.len() - 1;
    
    while low <= high
        invariant
            low <= a.len(),
            high < a.len(),
            forall|i: int| 0 <= i < low ==> a.spec_index(i) < K,
            forall|i: int| (high as int) < i < a.len() ==> a.spec_index(i) > K,
            (exists|i: nat| i < a.len() && a.spec_index(i) == K) ==> 
                (exists|j: int| (low as int) <= j <= (high as int) && a.spec_index(j) == K)
        decreases high + 1 - low
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            // All elements from low to mid are < K due to sorted property
            assert(forall|i: int| (low as int) <= i <= (mid as int) ==> a.spec_index(i) < K) by {
                let mid_int = mid as int;
                let low_int = low as int;
                assert(forall|i: int| low_int <= i <= mid_int ==> {
                    if i < mid_int {
                        // Use the sorted property: i < mid and sorted => a[i] <= a[mid]
                        assert(i < mid_int < a.len());
                        assert(a.spec_index(i) <= a.spec_index(mid_int));
                        assert(a.spec_index(mid_int) < K);
                        assert(a.spec_index(i) < K);
                    } else {
                        // i == mid
                        assert(i == mid_int);
                        assert(a.spec_index(i) == a.spec_index(mid_int));
                        assert(a.spec_index(i) < K);
                    }
                });
            }
            low = mid + 1;
        } else {
            // a[mid] > K, so all elements from mid to high are > K
            assert(forall|i: int| (mid as int) <= i <= (high as int) ==> a.spec_index(i) > K) by {
                let mid_int = mid as int;
                let high_int = high as int;
                assert(forall|i: int| mid_int <= i <= high_int ==> {
                    if mid_int < i {
                        // Use the sorted property: mid < i and sorted => a[mid] <= a[i]
                        assert(mid_int < i < a.len());
                        assert(a.spec_index(mid_int) <= a.spec_index(i));
                        assert(a.spec_index(mid_int) > K);
                        assert(a.spec_index(i) > K);
                    } else {
                        // i == mid
                        assert(i == mid_int);
                        assert(a.spec_index(i) == a.spec_index(mid_int));
                        assert(a.spec_index(i) > K);
                    }
                });
            }
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    // At this point, low > high, so we've covered the entire array
    // Prove that K is not in the array
    assert(forall|i: nat| i < a.len() ==> a.spec_index(i) != K) by {
        assert(forall|i: nat| i < a.len() ==> {
            let idx = i as int;
            if idx < (low as int) {
                assert(a.spec_index(idx) < K);
                assert(a.spec_index(idx) != K);
            } else {
                // idx >= low > high, so idx > high
                assert(idx >= (low as int));
                assert((low as int) > (high as int));
                assert(idx > (high as int));
                assert(a.spec_index(idx) > K);
                assert(a.spec_index(idx) != K);
            }
        });
    }
    
    false
}

}