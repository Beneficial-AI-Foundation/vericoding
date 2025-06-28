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
        
        // Proof that the newly added element satisfies the postcondition
        assert(result.len() == i + 1);
        assert(result.index(i as int) == a[idx]);
        assert(result.index(i as int) == a.index((a.len() - 1 - i) as int));
        assert(result.index(i as int) == a.index((a.len() as int - 1) - i as int));
        
        // Proof that existing elements still satisfy the postcondition
        assert(forall|k: int| 0 <= k < i ==> result.index(k) == a.index((a.len() as int - 1) - k));
        
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(result.len() == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> result.index(k) == a.index((a.len() as int - 1) - k));
    
    result
}

}