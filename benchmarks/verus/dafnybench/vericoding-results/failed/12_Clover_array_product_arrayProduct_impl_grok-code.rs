use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::*;
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
    let mut c: Vec<int> = Vec::new();
    for i: usize in 0..a.len()
        invariant
            c@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> a@[j] * b@[j] == c@[j]
    {
        c.push(a[i] * b[i]);
    }
    c
}
// </vc-code>

fn main() {}

}