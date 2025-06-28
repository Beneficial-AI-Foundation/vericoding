use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySum(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len() && 
        forall|i: int| 0 <= i < c.len() ==> c.spec_index(i) == a.spec_index(i) + b.spec_index(i)
{
    let mut c = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            c.len() == i,
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < c.len() ==> c.spec_index(j) == a.spec_index(j) + b.spec_index(j)
    {
        let sum = a[i] + b[i];
        c.push(sum);
        
        // Proof assertions to help verification
        assert(c.len() == i + 1);
        assert(c.spec_index(i as int) == sum);
        assert(c.spec_index(i as int) == a.spec_index(i as int) + b.spec_index(i as int));
        
        i = i + 1;
    }
    
    c
}

}