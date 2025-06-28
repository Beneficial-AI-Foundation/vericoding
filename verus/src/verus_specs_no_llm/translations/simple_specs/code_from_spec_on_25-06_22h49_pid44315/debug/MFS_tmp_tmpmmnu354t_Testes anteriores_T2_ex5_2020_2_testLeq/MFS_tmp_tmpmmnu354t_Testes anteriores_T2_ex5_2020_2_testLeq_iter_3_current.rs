use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool) 
    ensures 
        result <==> (
            (a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)) || 
            (exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])
        )
{
    let mut i = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            i <= b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
            forall|k: int| 0 <= k < i ==> !(a@[k] < b@[k]),
            forall|k: int| 0 <= k < i ==> !(a@[k] > b@[k]),
    {
        if a[i] < b[i] {
            // Prove the exists clause
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int)) by {
                assert(forall|j: int| 0 <= j < i ==> a@[j] == b@[j]);
            };
            assert(a@[i as int] < b@[i as int]);
            return true;
        } else if a[i] > b[i] {
            // This case means leq should be false
            assert(a@[i as int] > b@[i as int]);
            // Prove that the postcondition's RHS is false
            assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int))) by {
                if a.len() <= b.len() {
                    assert(a@[i as int] != b@[i as int]);
                    assert(!(a@ == b@.subrange(0, a.len() as int)));
                }
            };
            assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
                a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                assert(forall|k: int| 0 <= k < a.len() && k < b.len() ==> 
                    !(a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
                    assert(forall|k: int| 0 <= k <= i ==> !(a@[k] < b@[k]));
                    assert(forall|k: int| k > i && k < a.len() && k < b.len() ==> 
                        !(a@.subrange(0, k) == b@.subrange(0, k)));
                };
            };
            return false;
        }
        i += 1;
    }
    
    // If we've compared all elements of the shorter sequence and they're equal,
    // then a <= b iff a.len() <= b.len()
    if a.len() <= b.len() {
        // Prove that a is a prefix of b
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == b@[j]);
        assert(a@ == b@.subrange(0, a.len() as int)) by {
            assert(a@.len() == a.len());
            assert(b@.subrange(0, a.len() as int).len() == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == b@.subrange(0, a.len() as int)[j]) by {
                assert(forall|j: int| 0 <= j < a.len() ==> b@.subrange(0, a.len() as int)[j] == b@[j]);
            };
            assert_seqs_equal!(a@, b@.subrange(0, a.len() as int));
        };
        true
    } else {
        // a.len() > b.len(), so leq is false
        assert(a.len() > b.len());
        assert(i == b.len());
        assert(!(a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)));
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && 
            a@.subrange(0, k) == b@.subrange(0, k) && a@[k] < b@[k])) by {
            assert(forall|k: int| 0 <= k < a.len() && k < b.len() ==> k < i);
            assert(forall|k: int| 0 <= k < i ==> !(a@[k] < b@[k]));
        };
        false
    }
}

fn test_leq() -> (result: int)
    ensures result == 0
{
    // Test cases to verify the function works correctly
    let a1: Vec<int> = Vec::new();
    let b1: Vec<int> = Vec::new();
    let result1 = leq(a1, b1);
    assert(result1); // empty vectors are equal
    
    0
}

}