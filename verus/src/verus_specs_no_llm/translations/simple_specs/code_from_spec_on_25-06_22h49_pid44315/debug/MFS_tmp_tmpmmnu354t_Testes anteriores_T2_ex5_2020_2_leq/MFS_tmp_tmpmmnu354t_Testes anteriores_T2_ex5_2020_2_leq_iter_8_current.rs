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
    {
        if a[i] < b[i] {
            // Found position where a[i] < b[i]
            assert(exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k)) by {
                assert(0 <= i < a.len() && i < b.len());
                assert(a.spec_index(i) < b.spec_index(i));
                
                // Prove that slices up to i are equal
                assert(a.spec_index(..i) =~= b.spec_index(..i)) by {
                    assert(a.spec_index(..i).len() == i);
                    assert(b.spec_index(..i).len() == i);
                    assert(forall|j: int| 0 <= j < i ==> #[trigger] a.spec_index(..i)[j] == a[j]);
                    assert(forall|j: int| 0 <= j < i ==> #[trigger] b.spec_index(..i)[j] == b[j]);
                    assert(forall|j: int| 0 <= j < i ==> a.spec_index(..i)[j] == b.spec_index(..i)[j]);
                }
            }
            return true;
        } else if a[i] > b[i] {
            // Found position where a[i] > b[i], so leq is false
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
                // No k can satisfy the condition since we found a[i] > b[i]
                assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) == b.spec_index(k));
                assert(a.spec_index(i) > b.spec_index(i));
                
                if exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k) {
                    let witness = choose|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k);
                    if witness < i {
                        assert(a.spec_index(witness) == b.spec_index(witness));
                        assert(a.spec_index(witness) < b.spec_index(witness));
                        assert(false);
                    } else if witness == i {
                        assert(a.spec_index(i) < b.spec_index(i));
                        assert(a.spec_index(i) > b.spec_index(i));
                        assert(false);
                    } else {
                        // witness > i, but then the prefix wouldn't be equal
                        assert(false);
                    }
                }
            }
            
            assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
                // Can't be true since we found differing elements
                if a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()) {
                    assert(a.spec_index(i) == b.spec_index(i));
                    assert(a.spec_index(i) > b.spec_index(i));
                    assert(false);
                }
            }
            return false;
        }
        i += 1;
    }
    
    // If we reach here, all compared elements are equal
    let result = a.len() <= b.len();
    
    if result {
        // a.len() <= b.len() and a is a prefix of b
        assert(a.len() <= b.len());
        
        assert(a.spec_index(..) =~= b.spec_index(..a.len())) by {
            assert(i >= a.len() || i >= b.len());
            assert(a.len() <= b.len());
            assert(i >= a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
            
            assert(a.spec_index(..).len() == a.len());
            assert(b.spec_index(..a.len()).len() == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> #[trigger] a.spec_index(..).spec_index(j) == a.spec_index(j));
            assert(forall|j: int| 0 <= j < a.len() ==> #[trigger] b.spec_index(..a.len()).spec_index(j) == b.spec_index(j));
            assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(..).spec_index(j) == b.spec_index(..a.len()).spec_index(j));
        }
    } else {
        // a.len() > b.len()
        assert(a.len() > b.len());
        assert(i >= b.len());
        
        // First part of disjunction is false
        assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len())));
        
        // Second part is false because no such k exists
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
            // We compared all elements up to b.len() and found them equal
            assert(forall|j: int| 0 <= j < b.len() ==> a.spec_index(j) == b.spec_index(j));
            
            if exists|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k) {
                let witness = choose|k: int| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k);
                assert(0 <= witness < b.len());
                assert(a.spec_index(witness) == b.spec_index(witness));
                assert(a.spec_index(witness) < b.spec_index(witness));
                assert(false);
            }
        }
    }
    
    result
}

}