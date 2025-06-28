use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    requires
        exists|i: int| 0<=i<a.len() && a.spec_index(i)==e
    ensures
        0<=n<a.len() && a.spec_index(n)==e,
        forall|k: int| 0 <= k < n ==> a.spec_index(k)!=e
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) != e,
            exists|j: int| 0 <= j < a.len() && a.spec_index(j) == e
    {
        if a[i] == e {
            return i as int;
        }
        i = i + 1;
    }
    
    // This point should never be reached due to the precondition
    proof {
        // After the loop, we have checked all positions 0..a.len()
        assert(i == a.len());
        // The loop invariant tells us no element in 0..i equals e
        assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) != e);
        // Since i == a.len(), this means no element in the entire array equals e
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) != e);
        // But the precondition guarantees there exists such an element
        assert(exists|j: int| 0 <= j < a.len() && a.spec_index(j) == e);
        
        // Use the contradiction to prove false
        let witness_j = choose|j: int| 0 <= j < a.len() && a.spec_index(j) == e;
        assert(0 <= witness_j < a.len() && a.spec_index(witness_j) == e);
        assert(a.spec_index(witness_j) != e); // from the forall above
        assert(false);
    }
    
    arbitrary()  // Since we proved false, we can return any value
}

}