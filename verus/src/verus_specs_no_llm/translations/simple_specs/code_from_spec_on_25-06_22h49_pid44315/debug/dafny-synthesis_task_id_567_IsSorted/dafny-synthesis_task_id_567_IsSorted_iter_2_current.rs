use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSorted(a: Vec<int>) -> (sorted: bool)
    requires
        a.len() > 0
    ensures
        sorted <==> forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        !sorted ==> exists i, j :: 0 <= i < j < a.len() && a.spec_index(i) > a.spec_index(j)
{
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall k, l :: 0 <= k < l < i + 1 ==> a.spec_index(k) <= a.spec_index(l),
            forall k :: 0 <= k < i ==> a.spec_index(k) <= a.spec_index(k + 1)
    {
        if a[i] > a[i + 1] {
            assert(a.spec_index(i) > a.spec_index(i + 1));
            assert(0 <= i < i + 1 < a.len());
            return false;
        }
        i = i + 1;
    }
    
    // Prove that if we reach here, the array is sorted
    assert(forall k :: 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
    
    // Prove transitivity: if adjacent elements are in order, then all pairs are in order
    assert(forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)) by {
        // This follows from the fact that adjacent elements are in order
        // and transitivity of <=
    };
    
    return true;
}

}