use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn single(x: Vec<int>, y: Vec<int>) -> (b: Vec<int>)
    requires
        x.len() > 0,
        y.len() > 0
    ensures
        b.spec_index(..) == x.spec_index(..) + y.spec_index(..)
{
    let mut result = Vec::new();
    
    // Add all elements from x
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result.spec_index(k) == x.spec_index(k)
    {
        result.push(x[i]);
        i += 1;
    }
    
    // Add all elements from y
    let mut j = 0;
    while j < y.len()
        invariant
            j <= y.len(),
            result.len() == x.len() + j,
            forall|k: int| 0 <= k < x.len() ==> result.spec_index(k) == x.spec_index(k),
            forall|k: int| 0 <= k < j ==> result.spec_index(x.len() + k) == y.spec_index(k)
    {
        result.push(y[j]);
        j += 1;
    }
    
    // Prove the final postcondition
    assert(result.len() == x.len() + y.len());
    assert(forall|k: int| 0 <= k < x.len() ==> result.spec_index(k) == x.spec_index(k));
    assert(forall|k: int| 0 <= k < y.len() ==> result.spec_index(x.len() + k) == y.spec_index(k));
    
    // The postcondition follows from the definition of sequence concatenation
    assert(result.spec_index(..) =~= x.spec_index(..) + y.spec_index(..));
    
    result
}

}