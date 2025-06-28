use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result <==> (a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len())) || (exists k :: 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))
{
    let mut i = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            a.spec_index(..i) == b.spec_index(..i),
    {
        if a[i] < b[i] {
            assert(a.spec_index(..i) == b.spec_index(..i) && a.spec_index(i) < b.spec_index(i));
            assert(exists k :: 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k)) by {
                assert(0 <= i < a.len() && i < b.len() && a.spec_index(..i) == b.spec_index(..i) && a.spec_index(i) < b.spec_index(i));
            }
            return true;
        } else if a[i] > b[i] {
            assert(a.spec_index(..i) == b.spec_index(..i) && a.spec_index(i) > b.spec_index(i));
            assert(!(exists k :: 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
                assert(forall|k| 0 <= k < a.len() && k < b.len() ==> !(a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
                    assert(forall|k| 0 <= k < i ==> a.spec_index(k) == b.spec_index(k));
                    assert(a.spec_index(i) > b.spec_index(i));
                }
            }
            assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
                assert(a.spec_index(i) != b.spec_index(i));
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
        assert(a.spec_index(..) == b.spec_index(..a.len())) by {
            assert(forall|k| 0 <= k < a.len() ==> a.spec_index(k) == b.spec_index(k));
        }
        assert(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()));
    } else {
        // a.len() > b.len(), so b is a proper prefix of a
        assert(b.len() < a.len());
        assert(a.spec_index(..b.len()) == b.spec_index(..));
        // Since b is a proper prefix of a, a is lexicographically greater
        assert(!(exists k :: 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
            assert(forall|k| 0 <= k < b.len() ==> a.spec_index(k) == b.spec_index(k));
        }
        assert(!(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()))) by {
            assert(a.len() > b.len());
        }
    }
    
    result
}

}