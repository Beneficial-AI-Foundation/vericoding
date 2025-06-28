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
            assert(forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j));
            assert(a.spec_index(..i) =~= b.spec_index(..i)) by {
                assert(forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j));
                assert(a.spec_index(..i).len() == i);
                assert(b.spec_index(..i).len() == i);
            }
            assert(a.spec_index(i) < b.spec_index(i));
            assert(0 <= i < a.len() && i < b.len());
            assert(exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k)) by {
                assert(a.spec_index(..i) == b.spec_index(..i) && a.spec_index(i) < b.spec_index(i));
            }
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
        assert(i == a.len() || i == b.len());
        assert(i <= a.len() && i <= b.len());
        assert(forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j));
        
        if i == a.len() {
            assert(a.spec_index(..) =~= b.spec_index(..a.len())) by {
                assert(forall|j| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
                assert(a.spec_index(..).len() == a.len());
                assert(b.spec_index(..a.len()).len() == a.len());
            }
        } else {
            assert(i == b.len());
            assert(a.len() <= b.len());
            assert(forall|j| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j)) by {
                assert(forall|j| 0 <= j < i ==> a.spec_index(j) == b.spec_index(j));
                assert(i == b.len() && a.len() <= b.len());
            }
            assert(a.spec_index(..) =~= b.spec_index(..a.len())) by {
                assert(forall|j| 0 <= j < a.len() ==> a.spec_index(j) == b.spec_index(j));
                assert(a.spec_index(..).len() == a.len());
                assert(b.spec_index(..a.len()).len() == a.len());
            }
        }
        assert(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()));
    } else {
        // a.len() > b.len(), so b is a proper prefix of a
        assert(a.len() > b.len());
        assert(i == b.len());
        assert(forall|j| 0 <= j < b.len() ==> a.spec_index(j) == b.spec_index(j));
        
        // Since all elements of b match the corresponding elements of a,
        // there's no position where a[k] < b[k]
        assert(!(exists|k| 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))) by {
            assert(forall|k| 0 <= k < b.len() ==> a.spec_index(k) == b.spec_index(k));
        }
    }
    
    result
}

}