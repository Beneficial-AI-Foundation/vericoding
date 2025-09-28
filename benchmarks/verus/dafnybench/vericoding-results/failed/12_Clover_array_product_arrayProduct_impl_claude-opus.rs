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
    let n = a.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            c.len() == i,
            n == a.len(),
            n == b.len(),
            forall|j: int| #![auto] 0 <= j < i ==> c@[j] == (a@[j] as int) * (b@[j] as int),
        decreases n - i,
    {
        let product = a[i].wrapping_mul(b[i]);
        c.push(product);
        
        assert(c.len() == i + 1);
        assert(c@[i as int] == (a@[i as int] as int) * (b@[i as int] as int)) by {
            assert(c@.last() == product);
            assert(product == a[i].wrapping_mul(b[i]));
        }
        
        i = i + 1;
    }
    
    assert(c.len() == n);
    assert(forall|j: int| #![auto] 0 <= j < n ==> c@[j] == (a@[j] as int) * (b@[j] as int));
    
    c
}
// </vc-code>

fn main() {}

}