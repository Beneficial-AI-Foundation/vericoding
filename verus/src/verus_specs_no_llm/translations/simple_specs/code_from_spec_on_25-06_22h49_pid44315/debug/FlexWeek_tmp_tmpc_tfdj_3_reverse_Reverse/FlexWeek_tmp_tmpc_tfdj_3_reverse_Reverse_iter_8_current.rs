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
        
        // Prove bounds for the new element
        assert(0 <= i < a.len());
        assert(0 <= idx < a.len());
        assert(idx as int == (a.len() as int - 1) - i as int);
        
        // Prove the invariant holds for the new element
        assert(result.len() == i + 1);
        assert(result.index(i as int) == a[idx]);
        assert(result.index(i as int) == a.index(idx as int));
        assert(result.index(i as int) == a.index((a.len() as int - 1) - i as int));
        
        // Prove the invariant holds for existing elements
        assert(forall|k: int| 0 <= k < i ==> result.index(k) == a.index((a.len() as int - 1) - k)) by {
            // This follows from the loop invariant before the iteration
        };
        
        i = i + 1;
    }
    
    // At this point i == a.len(), so the postcondition follows from the loop invariant
    assert(result.len() == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> result.index(k) == a.index((a.len() as int - 1) - k));
    
    result
}

}