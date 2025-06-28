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
            forall|i: int| high < i < a.len() ==> a.spec_index(i) > K,
            (exists|i: nat| i < a.len() && a.spec_index(i) == K) ==> 
                (exists|j: int| low <= j <= high && a.spec_index(j) == K)
        decreases high + 1 - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            // Prove that all elements from low to mid are < K
            assert(forall|i: int| low <= i <= mid ==> a.spec_index(i) < K) by {
                let sorted_prop = isSorted(a);
                assert(forall|i: int| low <= i <= mid ==> {
                    &&& 0 <= i < a.len()
                    &&& 0 <= mid < a.len()
                    &&& i <= mid
                    &&& (i < mid ==> a.spec_index(i) <= a.spec_index(mid))
                    &&& (i == mid ==> a.spec_index(i) == a.spec_index(mid))
                    &&& a.spec_index(mid) < K
                    &&& a.spec_index(i) < K
                });
            }
            low = mid + 1;
        } else {
            // a[mid] > K
            // Prove that all elements from mid to high are > K
            assert(forall|i: int| mid <= i <= high ==> a.spec_index(i) > K) by {
                let sorted_prop = isSorted(a);
                assert(forall|i: int| mid <= i <= high ==> {
                    &&& 0 <= i < a.len()
                    &&& 0 <= mid < a.len()
                    &&& mid <= i
                    &&& (mid < i ==> a.spec_index(mid) <= a.spec_index(i))
                    &&& (mid == i ==> a.spec_index(mid) == a.spec_index(i))
                    &&& a.spec_index(mid) > K
                    &&& a.spec_index(i) > K
                });
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
        assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < K);
        assert(forall|i: int| high < i < a.len() ==> a.spec_index(i) > K);
        assert(forall|i: nat| i < a.len() ==> {
            let idx = i as int;
            &&& 0 <= idx < a.len()
            &&& (idx < low || high < idx)
            &&& (idx < low ==> a.spec_index(idx) < K)
            &&& (high < idx ==> a.spec_index(idx) > K)
            &&& a.spec_index(idx) != K
        });
    }
    
    false
}

}