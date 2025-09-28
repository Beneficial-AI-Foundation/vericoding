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
    let mut c = Vec::new();
    
    // Copy elements from array a
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c.len() == i,
            forall|j: int| 0 <= j < i ==> c[j] == a[j],
        decreases a.len() - i,
    {
        c.push(a[i]);
        i += 1;
    }
    
    // Copy elements from array b
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            c.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
            forall|k: int| 0 <= k < j ==> c[a.len() + k] == b[k],
        decreases b.len() - j,
    {
        c.push(b[j]);
        j += 1;
    }
    
    c
}
// </vc-code>

fn main() {
}

}