use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn BinarySearch(a: Vec<int>, key: int) -> (n: int)
    requires
        forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    ensures
        0 <= n <= a.len(),
        forall i :: 0 <= i < n ==> a.spec_index(i) < key,
        forall i :: n <= i < a.len() ==> key <= a.spec_index(i)
{
    let mut low: int = 0;
    let mut high: int = a.len() as int;
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall i :: 0 <= i < low ==> a.spec_index(i) < key,
            forall i :: high <= i < a.len() ==> key <= a.spec_index(i)
    {
        let mid = low + (high - low) / 2;
        
        if a.spec_index(mid) < key {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    low
}

}