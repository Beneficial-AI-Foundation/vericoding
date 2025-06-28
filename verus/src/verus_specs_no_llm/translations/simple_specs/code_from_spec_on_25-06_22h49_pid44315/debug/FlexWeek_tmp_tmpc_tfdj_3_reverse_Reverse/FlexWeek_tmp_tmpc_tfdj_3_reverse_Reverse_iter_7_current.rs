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
        
        // Prove that the invariant is maintained
        assert(result.len() == i + 1);
        assert(forall|k: int| 0 <= k < i ==> result.index(k) == a.index((a.len() as int - 1) - k));
        assert(result.index(i as int) == a.index(idx as int));
        assert(idx as int == (a.len() as int - 1) - i as int);
        
        i = i + 1;
    }
    
    result
}

}