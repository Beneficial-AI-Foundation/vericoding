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
            forall|j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) + b.spec_index(j)
    {
        // Help Verus understand the bounds
        assert(i < a.len());
        assert(i < b.len());
        assert(i as int < a.len());
        assert(i as int < b.len());
        
        let sum = a[i] + b[i];
        c.push(sum);
        
        // Proof assertions to help Verus verify the loop invariant
        assert(c.len() == i + 1);
        assert(c.spec_index(i as int) == sum);
        assert(c.spec_index(i as int) == a.spec_index(i as int) + b.spec_index(i as int));
        
        // Help maintain the invariant for all previous elements
        assert(forall|j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) + b.spec_index(j));
        
        i = i + 1;
        
        // Assert the invariant explicitly after increment
        assert(c.len() == i);
        assert(forall|j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) + b.spec_index(j));
    }
    
    // Final assertions to help establish postcondition
    assert(i == a.len());
    assert(c.len() == a.len());
    assert(forall|j: int| 0 <= j < c.len() ==> c.spec_index(j) == a.spec_index(j) + b.spec_index(j));
    
    c
}

}