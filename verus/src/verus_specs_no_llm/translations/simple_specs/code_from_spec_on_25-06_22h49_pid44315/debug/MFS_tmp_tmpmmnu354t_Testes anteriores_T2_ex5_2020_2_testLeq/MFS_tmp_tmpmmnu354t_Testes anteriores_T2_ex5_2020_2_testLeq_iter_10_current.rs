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
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    {
        if a[i] < b[i] {
            // Found first position where a[i] < b[i]
            return true;
            
        } else if a[i] > b[i] {
            // Found first position where a[i] > b[i]
            return false;
        }
        i = i + 1;
    }
    
    // Loop ended: all compared elements are equal
    // Return true iff a.len() <= b.len()
    a.len() <= b.len()
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