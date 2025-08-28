use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn append_array(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == c[i],
        forall|i: int| 0 <= i < b.len() ==> b[i] == c[a.len() + i],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut c = Vec::new();
    
    for i in 0..a.len()
        invariant
            c.len() == i,
            forall|j: int| 0 <= j < i ==> a[j] == c[j],
    {
        c.push(a[i]);
    }
    
    for i in 0..b.len()
        invariant
            c.len() == a.len() + i,
            forall|j: int| 0 <= j < a.len() ==> a[j] == c[j],
            forall|j: int| 0 <= j < i ==> b[j] == c[a.len() + j],
    {
        c.push(b[i]);
    }
    
    c
}
// </vc-code>

fn main() {
}

}