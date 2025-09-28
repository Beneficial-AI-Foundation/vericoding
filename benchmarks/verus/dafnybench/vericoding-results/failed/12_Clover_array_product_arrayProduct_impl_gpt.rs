use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let s: Seq<i32> = Seq::new(a.len(), |k: int| a@[k] * b@[k]);
    let c = Vec::from_seq(s);
    c
}
// </vc-code>

fn main() {}

}