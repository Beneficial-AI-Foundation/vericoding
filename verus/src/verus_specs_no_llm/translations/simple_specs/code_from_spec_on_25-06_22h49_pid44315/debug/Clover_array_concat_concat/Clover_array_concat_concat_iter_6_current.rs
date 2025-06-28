use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn concat(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures
        c.len() == b.len() + a.len(),
        forall|k: int| 0 <= k < a.len() ==> c.spec_index(k) == a.spec_index(k),
        forall|k: int| 0 <= k < b.len() ==> c.spec_index(k + a.len()) == b.spec_index(k)
{
    let mut result = Vec::new();
    
    // First, add all elements from vector a
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result.spec_index(k) == a.spec_index(k)
    {
        result.push(a[i]);
        i = i + 1;
    }
    
    // Then, add all elements from vector b
    let mut j: usize = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            result.len() == a.len() + j,
            // Elements from a are preserved
            forall|k: int| 0 <= k < a.len() ==> result.spec_index(k) == a.spec_index(k),
            // Elements from b added so far
            forall|k: int| 0 <= k < j ==> result.spec_index(k + a.len()) == b.spec_index(k)
    {
        result.push(b[j]);
        j = j + 1;
    }
    
    result
}

}