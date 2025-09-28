use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn concat(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == b.len() + a.len(),
        forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> c[k + a.len()] == b[k],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::new();
    
    // Copy elements from a
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c.len() == i,
            forall|k: int| 0 <= k < i ==> c[k] == a[k],
        decreases a.len() - i,
    {
        c.push(a[i]);
        i += 1;
    }
    
    // Copy elements from b
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            c.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
            forall|k: int| 0 <= k < j ==> c[k + a.len()] == b[k],
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