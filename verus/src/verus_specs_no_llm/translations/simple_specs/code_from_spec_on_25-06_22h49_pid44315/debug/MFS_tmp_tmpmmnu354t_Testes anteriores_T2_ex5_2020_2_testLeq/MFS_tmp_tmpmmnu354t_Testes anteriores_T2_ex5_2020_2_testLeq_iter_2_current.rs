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
    {
        if a[i] < b[i] {
            // Prove the exists clause
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int));
            assert(a@[i as int] < b@[i as int]);
            return true;
        } else if a[i] > b[i] {
            // This case means leq should be false
            assert(a@[i as int] > b@[i as int]);
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
            assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == b@.subrange(0, a.len() as int)[j]);
        };
        true
    } else {
        // a.len() > b.len(), so leq is false
        // We need to show that neither condition in the postcondition holds
        assert(a.len() > b.len());
        assert(i == b.len());
        false
    }
}

fn test_leq() -> (result: int)
    ensures result == 0
{
    // Test cases to verify the function works correctly
    let a1 = vec![1, 2, 3];
    let b1 = vec![1, 2, 3, 4];
    let result1 = leq(a1, b1);
    assert(result1); // a1 is prefix of b1
    
    let a2 = vec![1, 2, 4];
    let b2 = vec![1, 2, 3];
    let result2 = leq(a2, b2);
    assert(!result2); // a2[2] > b2[2]
    
    let a3 = vec![1, 2];
    let b3 = vec![1, 3];
    let result3 = leq(a3, b3);
    assert(result3); // a3[1] < b3[1]
    
    0
}

}