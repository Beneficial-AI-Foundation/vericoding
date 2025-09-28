use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn append_array(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == c[i],
        forall|i: int| 0 <= i < b.len() ==> b[i] == c[a.len() + i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
    {
        result.push(a[i]);
    }
    
    for i in 0..b.len()
        invariant
            result.len() == a.len() + i,
            forall|j: int| 0 <= j < a.len() ==> result[j] == a[j],
            forall|j: int| 0 <= j < i ==> result[a.len() + j] == b[j],
    {
        result.push(b[i]);
    }
    
    result
}
// </vc-code>

fn main() {
}

}