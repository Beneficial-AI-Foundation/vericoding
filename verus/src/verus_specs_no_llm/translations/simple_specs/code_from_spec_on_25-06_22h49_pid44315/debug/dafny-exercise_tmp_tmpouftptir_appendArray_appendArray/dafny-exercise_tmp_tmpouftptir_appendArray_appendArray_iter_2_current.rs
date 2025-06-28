use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn appendArray(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures
        c.len() == a.len() + b.len(),
        forall |i: int| 0 <= i < a.len() ==> a.spec_index(i) == c.spec_index(i),
        forall |i: int| 0 <= i < b.len() ==> b.spec_index(i) == c.spec_index(a.len() + i)
{
    let mut result = Vec::new();
    
    // Append elements from vector a
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result.spec_index(j) == a.spec_index(j)
    {
        result.push(a[i as usize]);
        i = i + 1;
    }
    
    // Append elements from vector b
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            result.len() == a.len() + j,
            forall |k: int| 0 <= k < a.len() ==> result.spec_index(k) == a.spec_index(k),
            forall |k: int| 0 <= k < j ==> result.spec_index(a.len() + k) == b.spec_index(k)
    {
        result.push(b[j as usize]);
        j = j + 1;
    }
    
    result
}

}