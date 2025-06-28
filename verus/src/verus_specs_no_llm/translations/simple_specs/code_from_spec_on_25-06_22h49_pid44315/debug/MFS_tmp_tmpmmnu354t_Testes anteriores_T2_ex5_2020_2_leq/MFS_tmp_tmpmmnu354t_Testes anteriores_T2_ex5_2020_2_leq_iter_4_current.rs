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
    {
        if a[i] < b[i] {
            assert(a.spec_index(..i) =~= b.spec_index(..i)) by {
                assert(forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j));
            }
            assert(a.spec_index(i) < b.spec_index(i));
            assert(0 <= i < a.len() && i < b.len());
            return true;
        } else if a[i] > b[i] {
            return false;
        }
        i += 1;
    }
    
    // If we reach here, all compared elements are equal
    let result = a.len() <= b.len();
    
    if result {
        // a.len() <= b.len() and a is a prefix of b
        assert(a.len() <= b.len());
        
        // We need to prove that a is exactly b[..a.len()]
        assert(a.spec_index(..) =~= b.spec_index(..a.len())) by {
            if a.len() <= b.len() {
                // Case 1: i reached a.len() (we exhausted a)
                if i == a.len() {
                    assert(forall|j| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
                } else {
                    // Case 2: i reached b.len() but a.len() <= b.len()
                    assert(i == b.len());
                    assert(a.len() <= b.len());
                    // Since the loop ended with i == b.len() and a.len() <= b.len(),
                    // we must have i >= a.len() as well, so i == a.len()
                    assert(i >= a.len());
                    assert(i == a.len()) by {
                        assert(i == b.len() && a.len() <= b.len() && i < a.len() ==> false);
                    }
                    assert(forall|j| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
                }
            }
        }
    } else {
        // a.len() > b.len()
        assert(a.len() > b.len());
        assert(i == b.len());
        
        // In this case, the first part of the disjunction is false
        assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
            assert(a.len() > b.len());
        }
        
        // The second part is also false because we never found a position where a[k] < b[k]
        assert(!(exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
            // We know that for all compared positions, a[k] >= b[k]
            // and we only exit the loop when a[k] == b[k] for all compared k
            assert(forall|k| 0 <= k < b.len() ==> a.spec_index(k) == b.spec_index(k));
        }
    }
    
    result
}

}