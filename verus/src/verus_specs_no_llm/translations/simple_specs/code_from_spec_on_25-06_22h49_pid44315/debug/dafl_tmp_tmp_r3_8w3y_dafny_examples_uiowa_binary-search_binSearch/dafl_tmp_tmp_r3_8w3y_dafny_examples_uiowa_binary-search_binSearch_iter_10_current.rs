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
            forall|i: int| 0 <= i < (low as int) ==> a.spec_index(i) < K,
            forall|i: int| (high as int) < i < a.len() ==> a.spec_index(i) > K,
            (exists|i: nat| i < a.len() && a.spec_index(i) == K) ==> 
                (exists|j: int| (low as int) <= j <= (high as int) && j < a.len() && a.spec_index(j) == K)
        decreases high + 1 - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        assert(mid < a.len());
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            // Prove all elements from low to mid are < K using sortedness
            assert(forall|i: int| (low as int) <= i <= (mid as int) ==> a.spec_index(i) <= a.spec_index(mid as int));
            assert(a.spec_index(mid as int) < K);
            assert(forall|i: int| (low as int) <= i <= (mid as int) ==> a.spec_index(i) < K);
            
            low = mid + 1;
            
        } else {
            // a[mid] > K
            // Prove all elements from mid to high are > K using sortedness
            assert(forall|i: int| (mid as int) <= i <= (high as int) ==> a.spec_index(mid as int) <= a.spec_index(i));
            assert(a.spec_index(mid as int) > K);
            assert(forall|i: int| (mid as int) <= i <= (high as int) ==> a.spec_index(i) > K);
            
            if mid == 0 {
                return false;
            }
            high = mid - 1;
        }
    }
    
    // Loop exited, so low > high
    // The invariants guarantee that all elements < low are < K
    // and all elements > high are > K
    // Since low > high, all elements are either < K or > K, so none equal K
    assert(forall|i: int| 0 <= i < a.len() ==> 
        (i < (low as int) && a.spec_index(i) < K) || 
        (i > (high as int) && a.spec_index(i) > K));
    
    false
}

}