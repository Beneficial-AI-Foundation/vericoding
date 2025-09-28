use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty helpers, as no additional proofs or code are needed for this fix.
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &mut Vec<i32>)
    requires 
        old(a).len() >= 8,
    ensures 
        old(a)[4] + 3 == a[4],
        a[7] == 516,
        forall|i: int| 0 <= i < a.len() ==> i != 7 && i != 4 ==> a[i] == old(a)[i],
        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    let old_a4 = a[4];
    a[4] = old_a4 + 3;
    a[7] = 516;
}
// </vc-code>

fn main() {}

}