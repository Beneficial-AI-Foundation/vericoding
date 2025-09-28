use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix.
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::new();
    for i in 0..a.len()
        invariant
            0 <= (i as int) <= a@.len(),
            c@.len() == i as int,
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] c@[j] == a@[j] + b@[j],
    {
        c.push(a[i] + b[i]);
    }
    c
}
// </vc-code>

fn main() {}

}