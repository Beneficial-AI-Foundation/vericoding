use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn arrayProduct(a: Vec<i32>, b: Vec<i32>) -> (c: Vec<i32>)
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> a.spec_index(i) * b.spec_index(i) == c.spec_index(i)
{
    let mut c = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            a.len() == b.len(),
            forall |j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) * b.spec_index(j)
    {
        let product = a[i] * b[i];
        c.push(product);
        
        // Help Verus understand the relationship between the pushed value and spec_index
        assert(c.len() == i + 1);
        assert(c.spec_index(i as int) == product);
        assert(product == a.spec_index(i as int) * b.spec_index(i as int));
        
        // Prove that the invariant holds for all previous elements
        assert(forall |j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) * b.spec_index(j)) by {
            // This follows from the loop invariant before the push
        };
        
        i = i + 1;
        
        // Prove the invariant for the next iteration
        assert(forall |j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) * b.spec_index(j)) by {
            assert(forall |j: int| 0 <= j < (i-1) ==> c.spec_index(j) == a.spec_index(j) * b.spec_index(j));
            assert(c.spec_index((i-1) as int) == a.spec_index((i-1) as int) * b.spec_index((i-1) as int));
        };
    }
    
    // Final assertion to help prove the postcondition
    assert(c.len() == a.len());
    assert(forall |j: int| 0 <= j < a.len() ==> c.spec_index(j) == a.spec_index(j) * b.spec_index(j));
    
    c
}

}