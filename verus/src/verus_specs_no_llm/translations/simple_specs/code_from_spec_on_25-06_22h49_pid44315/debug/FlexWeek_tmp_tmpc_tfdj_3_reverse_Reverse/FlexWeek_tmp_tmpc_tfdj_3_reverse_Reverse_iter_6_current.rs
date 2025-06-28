use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() ==> b.index(k) == a.index((a.len() as int - 1) - k)
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result.index(k) == a.index((a.len() as int - 1) - k)
    {
        let idx = a.len() - 1 - i;
        result.push(a[idx]);
        
        // Help the verifier with the index relationship
        assert(idx < a.len());
        assert(idx == a.len() - 1 - i);
        
        // Prove the postcondition holds for the new element
        assert(result.len() == i + 1);
        assert(result[i as int] == a[idx as int]);
        assert((a.len() as int - 1) - (i as int) == idx as int);
        
        i = i + 1;
    }
    
    // Final assertion to help prove postcondition
    assert(result.len() == a.len());
    assert(forall|k: int| 0 <= k < result.len() ==> 
        result.index(k) == a.index((a.len() as int - 1) - k));
    
    result
}

}