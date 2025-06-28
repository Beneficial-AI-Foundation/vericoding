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
            forall|i: nat| i < low ==> a.spec_index(i) < K,
            forall|i: nat| high < i < a.len() ==> a.spec_index(i) > K,
            (exists|i: nat| i < a.len() && a.spec_index(i) == K) ==> 
                (exists|j: nat| low <= j <= high && a.spec_index(j) == K)
        decreases high + 1 - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            // Prove that all elements from low to mid are < K
            assert(forall|i: nat| low <= i <= mid ==> a.spec_index(i) < K) by {
                assert(forall|i: nat| low <= i <= mid ==> a.spec_index(i) <= a.spec_index(mid)) by {
                    assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j));
                    assert(forall|i: nat| low <= i <= mid ==> i <= mid);
                }
                assert(a.spec_index(mid) < K);
            }
            low = mid + 1;
        } else {
            // a[mid] > K
            // Prove that all elements from mid to high are > K
            assert(forall|i: nat| mid <= i <= high ==> a.spec_index(i) > K) by {
                assert(forall|i: nat| mid <= i <= high ==> a.spec_index(mid) <= a.spec_index(i)) by {
                    assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j));
                    assert(forall|i: nat| mid <= i <= high ==> mid <= i);
                }
                assert(a.spec_index(mid) > K);
            }
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    // At this point, we've exhausted the search space
    // Prove that K is not in the array
    assert(forall|i: nat| i < a.len() ==> a.spec_index(i) != K) by {
        assert(low > high);
        assert(forall|i: nat| i < low ==> a.spec_index(i) < K);
        assert(forall|i: nat| high < i < a.len() ==> a.spec_index(i) > K);
        assert(forall|i: nat| i < a.len() ==> (i < low || high < i)) by {
            assert(forall|i: nat| i < a.len() ==> !(low <= i <= high)) by {
                assert(low > high);
            }
        }
    }
    
    false
}

}