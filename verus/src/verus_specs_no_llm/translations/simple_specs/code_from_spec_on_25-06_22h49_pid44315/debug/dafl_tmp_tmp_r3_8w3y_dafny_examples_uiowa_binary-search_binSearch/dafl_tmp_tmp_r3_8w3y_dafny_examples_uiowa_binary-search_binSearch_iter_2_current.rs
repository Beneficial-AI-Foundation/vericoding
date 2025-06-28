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
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            // Prove that all elements from low to mid are < K
            assert(forall|i: nat| low <= i <= mid ==> a.spec_index(i) < K) by {
                // From sorted property and a[mid] < K
                assert(forall|i: nat| i <= mid ==> a.spec_index(i) <= a.spec_index(mid)) by {
                    assert(isSorted(a));
                }
            }
            low = mid + 1;
        } else {
            // a[mid] > K
            // Prove that all elements from mid to high are > K
            assert(forall|i: nat| mid <= i <= high ==> a.spec_index(i) > K) by {
                // From sorted property and a[mid] > K
                assert(forall|i: nat| mid <= i < a.len() ==> a.spec_index(mid) <= a.spec_index(i)) by {
                    assert(isSorted(a));
                }
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
        // All elements before low are < K
        // All elements after high are > K
        // low > high, so we've covered the entire array
    }
    
    false
}

}