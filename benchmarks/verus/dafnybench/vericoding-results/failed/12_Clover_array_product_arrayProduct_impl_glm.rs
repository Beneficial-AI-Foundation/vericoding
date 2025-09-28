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
    for i in 0..a.len()
        invariant
            c.len() == i,
            b.len() == a.len(),
            forall|j: int| #![auto] 0 <= j < i ==> c@[j] == a[j] * b[j],
    {
        let product = a[i] as i64 * b[i] as i64;
        assert(product >= i32::MIN as i64 && product <= i32::MAX as i64);
        c.push(product as i32);
    }
    c
}
// </vc-code>

fn main() {}

}