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
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        assert(mid < a.len());
        
        if a[mid] == K {
            assert(a.spec_index(mid as int) == K);
            assert(exists|i: nat| i < a.len() && a.spec_index(i) == K);
            return true;
        } else if a[mid] < K {
            // Use sorted property to prove all elements from low to mid are < K
            assert(forall|i: int| (low as int) <= i <= (mid as int) ==> a.spec_index(i) < K) by {
                assert(forall|i: int| (low as int) <= i <= (mid as int) ==> {
                    // Use sortedness: a[i] <= a[mid] < K
                    assert(0 <= i <= (mid as int) < a.len());
                    assert(a.spec_index(i) <= a.spec_index(mid as int));
                    assert(a.spec_index(mid as int) < K);
                    a.spec_index(i) < K
                });
            };
            
            low = mid + 1;
            
        } else {
            // a[mid] > K
            // Use sorted property to prove all elements from mid to high are > K  
            assert(forall|i: int| (mid as int) <= i <= (high as int) ==> a.spec_index(i) > K) by {
                assert(forall|i: int| (mid as int) <= i <= (high as int) ==> {
                    // Use sortedness: a[mid] <= a[i] and a[mid] > K
                    assert(0 <= (mid as int) <= i < a.len());
                    assert(a.spec_index(mid as int) <= a.spec_index(i));
                    assert(a.spec_index(mid as int) > K);
                    a.spec_index(i) > K
                });
            };
            
            if mid == 0 {
                // Special case: mid is 0, so all elements are > K
                assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) > K);
                assert(!(exists|i: nat| i < a.len() && a.spec_index(i) == K));
                return false;
            }
            high = mid - 1;
        }
    }
    
    // Loop exited, so low > high
    assert(low > high);
    
    // Prove that K is not in the array using the maintained invariants
    assert(!(exists|i: nat| i < a.len() && a.spec_index(i) == K)) by {
        assert(forall|i: nat| i < a.len() ==> a.spec_index(i) != K) by {
            assert(forall|i: nat| i < a.len() ==> {
                let idx = i as int;
                if idx < (low as int) {
                    // From invariant: elements before low are < K
                    assert(a.spec_index(idx) < K);
                    assert(a.spec_index(idx) != K);
                } else {
                    // idx >= low > high, so idx > high
                    assert(idx >= (low as int));
                    assert((low as int) > (high as int));
                    assert(idx > (high as int));
                    // From invariant: elements after high are > K
                    assert(a.spec_index(idx) > K);
                    assert(a.spec_index(idx) != K);
                }
                a.spec_index(idx) != K
            });
        };
    };
    
    false
}

}