use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PairwiseAddition(a: Vec<int>) -> (result: Vec<int>)
    requires
        a.len() % 2 == 0
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(2*i) + a.spec_index(2*i + 1)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i % 2 == 0,
            i <= a.len(),
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(2*j) + a.spec_index(2*j + 1)
    {
        // Prove bounds for safe indexing
        assert(i < a.len());
        assert(a.len() % 2 == 0);
        assert(i % 2 == 0);
        
        // Since a.len() is even and i is even and i < a.len(), we know i+1 < a.len()
        assert(i + 1 < a.len()) by {
            // If i < a.len() and a.len() is even and i is even, then i+1 < a.len()
            // because if i+1 >= a.len(), then i >= a.len()-1, but since a.len() is even
            // and i is even, this would mean i >= a.len(), contradicting i < a.len()
        };
        
        let sum = a[i] + a[i + 1];
        result.push(sum);
        
        // Prove arithmetic for the next iteration
        assert((i + 2) / 2 == i / 2 + 1) by {
            // Basic arithmetic: (i + 2) / 2 = i/2 + 2/2 = i/2 + 1
            // This holds for integer division when i is even
        };
        
        i = i + 2;
    }
    
    // Final assertion to help with the postcondition
    assert(i == a.len());
    assert(result.len() == a.len() / 2);
    
    result
}

}