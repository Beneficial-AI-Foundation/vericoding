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
        
        // Prove the invariant for the next iteration
        assert(result.len() == i + 1);
        assert(forall|k: int| 0 <= k < (i + 1) ==> result.index(k) == a.index((a.len() as int - 1) - k)) by {
            // For k < i, this follows from the previous invariant
            assert(forall|k: int| 0 <= k < i ==> result.index(k) == a.index((a.len() as int - 1) - k));
            
            // For k == i, we need to prove the newly added element
            let k = i as int;
            assert(result.index(k) == a[idx]);
            assert(idx as int == (a.len() as int - 1) - i as int);
            assert(result.index(k) == a.index((a.len() as int - 1) - k));
        };
        
        i = i + 1;
    }
    
    result
}

}