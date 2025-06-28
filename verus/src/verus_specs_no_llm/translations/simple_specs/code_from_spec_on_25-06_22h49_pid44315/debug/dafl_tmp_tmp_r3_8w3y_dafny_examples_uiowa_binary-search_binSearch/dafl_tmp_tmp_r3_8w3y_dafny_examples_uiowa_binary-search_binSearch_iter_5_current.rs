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
            0 <= low <= a.len(),
            high < a.len(),
            low <= high + 1,
            forall|i: int| 0 <= i < low ==> a.spec_index(i) < K,
            forall|i: int| high < i < a.len() ==> a.spec_index(i) > K,
            (exists|i: nat| i < a.len() && a.spec_index(i) == K) ==> 
                (exists|j: int| low <= j <= high && a.spec_index(j) == K)
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        assert(mid < a.len());
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            // All elements from low to mid are < K due to sorted property
            assert(forall|i: int| low <= i <= mid ==> a.spec_index(i) < K) by {
                assert(forall|i: int| low <= i <= mid ==> {
                    if i < mid {
                        // i < mid and array is sorted, so a[i] <= a[mid] < K
                        assert(a.spec_index(i) <= a.spec_index(mid)) by {
                            assert(isSorted(a));
                            assert(0 <= i < mid < a.len());
                        }
                        assert(a.spec_index(i) < K);
                    } else {
                        // i == mid
                        assert(i == mid);
                        assert(a.spec_index(i) == a.spec_index(mid));
                        assert(a.spec_index(i) < K);
                    }
                });
            }
            low = mid + 1;
        } else {
            // a[mid] > K, so all elements from mid to high are > K
            assert(forall|i: int| mid <= i <= high ==> a.spec_index(i) > K) by {
                assert(forall|i: int| mid <= i <= high ==> {
                    if mid < i {
                        // mid < i and array is sorted, so a[mid] <= a[i] and a[mid] > K
                        assert(a.spec_index(mid) <= a.spec_index(i)) by {
                            assert(isSorted(a));
                            assert(0 <= mid < i < a.len());
                        }
                        assert(a.spec_index(i) > K);
                    } else {
                        // i == mid
                        assert(i == mid);
                        assert(a.spec_index(i) == a.spec_index(mid));
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
    assert(low > high);
    
    // Prove that K is not in the array
    assert(forall|i: nat| i < a.len() ==> a.spec_index(i) != K) by {
        assert(forall|i: nat| i < a.len() ==> {
            let idx = i as int;
            if idx < low {
                assert(a.spec_index(idx) < K);
                assert(a.spec_index(idx) != K);
            } else {
                // idx >= low > high, so idx > high
                assert(idx > high);
                assert(high < idx < a.len());
                assert(a.spec_index(idx) > K);
                assert(a.spec_index(idx) != K);
            }
        });
    }
    
    false
}

}