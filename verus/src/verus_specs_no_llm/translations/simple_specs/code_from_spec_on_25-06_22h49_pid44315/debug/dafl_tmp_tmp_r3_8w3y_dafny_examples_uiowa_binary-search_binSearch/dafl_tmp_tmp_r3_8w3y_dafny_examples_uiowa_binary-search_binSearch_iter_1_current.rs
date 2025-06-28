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
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] == K {
            return true;
        } else if a[mid] < K {
            low = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    false
}

}