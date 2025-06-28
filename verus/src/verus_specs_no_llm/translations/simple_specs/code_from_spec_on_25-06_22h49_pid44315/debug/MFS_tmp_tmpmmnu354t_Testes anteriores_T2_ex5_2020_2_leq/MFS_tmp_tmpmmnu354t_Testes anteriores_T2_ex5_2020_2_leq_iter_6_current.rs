use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to compare slices
spec fn slices_equal(a: Vec<int>, b: Vec<int>, end: int) -> bool {
    end >= 0 && end <= a.len() && end <= b.len() &&
    forall|j: int| 0 <= j < end ==> a.spec_index(j) == b.spec_index(j)
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result <==> (a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len())) || (exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))
{
    let mut i = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j),
            forall|k: int| 0 <= k < i ==> !(a.spec_index(k) < b.spec_index(k)),
    {
        if a[i] < b[i] {
            // Found position where a[i] < b[i]
            assert(exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k)) by {
                assert(0 <= i < a.len() && i < b.len());
                assert(a.spec_index(i) < b.spec_index(i));
                assert(a.spec_index(..i) == b.spec_index(..i)) by {
                    let a_slice = a.spec_index(..i);
                    let b_slice = b.spec_index(..i);
                    assert(a_slice.len() == i);
                    assert(b_slice.len() == i);
                    assert(forall|j: int| 0 <= j < i ==> a_slice.spec_index(j) == a.spec_index(j));
                    assert(forall|j: int| 0 <= j < i ==> b_slice.spec_index(j) == b.spec_index(j));
                    assert(forall|j: int| 0 <= j < i ==> a_slice.spec_index(j) == b_slice.spec_index(j));
                }
            }
            return true;
        } else if a[i] > b[i] {
            // Found position where a[i] > b[i], so leq is false
            return false;
        }
        i += 1;
    }
    
    // If we reach here, all compared elements are equal
    let result = a.len() <= b.len();
    
    if result {
        // a.len() <= b.len() and a is a prefix of b
        assert(a.len() <= b.len());
        
        assert(a.spec_index(..) == b.spec_index(..a.len())) by {
            // The loop terminated, so either i == a.len() or i == b.len()
            // Since result is true, we have a.len() <= b.len()
            let min_len = if a.len() <= b.len() { a.len() } else { b.len() };
            assert(i >= min_len);
            assert(i >= a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
            
            let a_full = a.spec_index(..);
            let b_prefix = b.spec_index(..a.len());
            assert(a_full.len() == a.len());
            assert(b_prefix.len() == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> a_full.spec_index(j) == a.spec_index(j));
            assert(forall|j: int| 0 <= j < a.len() ==> b_prefix.spec_index(j) == b.spec_index(j));
            assert(forall|j: int| 0 <= j < a.len() ==> a_full.spec_index(j) == b_prefix.spec_index(j));
        }
    } else {
        // a.len() > b.len()
        assert(a.len() > b.len());
        
        // First part of disjunction is false
        assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
            assert(a.len() > b.len());
        }
        
        // Second part is false because no such k exists
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
            // We compared all elements up to b.len() and found them equal
            assert(i >= b.len());
            assert(forall|k: int| 0 <= k < b.len() ==> a.spec_index(k) == b.spec_index(k));
            // For any k < b.len(), we have a[k] == b[k], not a[k] < b[k]
            assert(forall|k: int| 0 <= k < b.len() ==> !(a.spec_index(k) < b.spec_index(k)));
            
            // Prove by contradiction
            if exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k) {
                let witness_k = choose|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k);
                assert(0 <= witness_k < b.len());
                assert(a.spec_index(witness_k) == b.spec_index(witness_k)); // from loop invariant
                assert(a.spec_index(witness_k) < b.spec_index(witness_k)); // from witness property
                assert(false); // contradiction
            }
        }
    }
    
    result
}

}