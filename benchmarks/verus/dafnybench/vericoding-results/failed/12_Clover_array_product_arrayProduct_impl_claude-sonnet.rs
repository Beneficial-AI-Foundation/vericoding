use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            forall|j: int| 0 <= j < i ==> a@[j] * b@[j] == c@[j],
        decreases a.len() - i,
    {
        assert(i < a.len());
        assert(0 <= i && i < a.len());
        let product = a[i as usize] * b[i as usize];
        c.push(product);
        i += 1;
    }
    
    c
}
// </vc-code>

fn main() {}

}