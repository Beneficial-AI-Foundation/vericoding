use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
            forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j),
            forall|k| 0 <= k < i ==> !(a.spec_index(k) < b.spec_index(k)),
    {
        if a[i] < b[i] {
            // Found position where a[i] < b[i]
            assert(exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k)) by {
                assert(0 <= i < a.len() && i < b.len());
                assert(a.spec_index(i) < b.spec_index(i));
                assert(a.spec_index(..i) =~= b.spec_index(..i)) by {
                    assert(forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j));
                }
            }
            return true;
        } else if a[i] > b[i] {
            // Found position where a[i] > b[i], so leq is false
            assert(!(exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
                // For contradiction, assume such k exists
                assert(forall|k| 0 <= k <= i ==> !(a.spec_index(k) < b.spec_index(k))) by {
                    assert(forall|k| 0 <= k < i ==> a.spec_index(k) == b.spec_index(k));
                    assert(a.spec_index(i) > b.spec_index(i));
                }
            }
            assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
                // If a.len() <= b.len() and a == b[..a.len()], then a[i] should equal b[i]
                if a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()) {
                    assert(i < a.len());
                    assert(a.spec_index(i) == b.spec_index(i));
                    assert(false); // contradiction with a[i] > b[i]
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
            // The loop terminated, so either i == a.len() or i == b.len()
            // Since result is true, we have a.len() <= b.len()
            // If i == b.len(), then i >= a.len() (since a.len() <= b.len())
            // In both cases, we've compared all elements of a
            let min_len = if a.len() <= b.len() { a.len() } else { b.len() };
            assert(i >= min_len);
            assert(i >= a.len());
            assert(forall|j| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
        }
    } else {
        // a.len() > b.len()
        assert(a.len() > b.len());
        assert(i == b.len());
        
        // First part of disjunction is false
        assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
            assert(a.len() > b.len());
        }
        
        // Second part is false because no such k exists
        assert(!(exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
            // We compared all elements up to b.len() and found them equal
            assert(forall|k| 0 <= k < b.len() ==> a.spec_index(k) == b.spec_index(k));
            // For any k < b.len(), we have a[k] == b[k], not a[k] < b[k]
            assert(forall|k| 0 <= k < b.len() ==> !(a.spec_index(k) < b.spec_index(k)));
        }
    }
    
    result
}

}