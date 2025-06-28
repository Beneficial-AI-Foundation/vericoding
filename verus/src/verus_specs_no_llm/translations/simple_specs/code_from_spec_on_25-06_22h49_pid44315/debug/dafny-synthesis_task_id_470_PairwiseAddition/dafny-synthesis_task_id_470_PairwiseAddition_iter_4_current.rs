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
    let mut i = 0;
    
    while i < a.len()
        invariant
            i % 2 == 0,
            i <= a.len(),
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(2*j) + a.spec_index(2*j + 1)
    {
        // Establish that i + 1 is within bounds
        assert(i + 1 < a.len());
        
        let sum = a[i] + a[i + 1];
        result.push(sum);
        
        // Help Verus understand the arithmetic
        assert((i + 2) / 2 == i / 2 + 1);
        
        i += 2;
    }
    
    result
}

}