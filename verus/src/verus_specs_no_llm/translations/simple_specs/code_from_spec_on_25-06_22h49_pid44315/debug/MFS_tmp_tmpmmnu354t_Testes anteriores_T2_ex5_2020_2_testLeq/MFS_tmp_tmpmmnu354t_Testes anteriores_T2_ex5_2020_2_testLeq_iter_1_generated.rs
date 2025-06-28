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
    {
        if a[i] < b[i] {
            return true;
        } else if a[i] > b[i] {
            return false;
        }
        i += 1;
    }
    
    // If we've compared all elements of the shorter sequence and they're equal,
    // then a <= b iff a.len() <= b.len()
    a.len() <= b.len()
}

fn test_leq() -> (result: int)
    ensures result == 0
{
    // Test cases to verify the function works correctly
    let a1 = vec![1, 2, 3];
    let b1 = vec![1, 2, 3, 4];
    assert(leq(a1, b1)); // a1 is prefix of b1
    
    let a2 = vec![1, 2, 4];
    let b2 = vec![1, 2, 3];
    assert(!leq(a2, b2)); // a2[2] > b2[2]
    
    let a3 = vec![1, 2];
    let b3 = vec![1, 3];
    assert(leq(a3, b3)); // a3[1] < b3[1]
    
    0
}

}