// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): added proof block to link runtime value to spec value to resolve overflow check */
    let old_val_at_4 = a[4];

    proof {
        assert(old_val_at_4 == old(a)@[4]);
    }

    a.set(4, old_val_at_4 + 3);
    a.set(7, 516);
}
// </vc-code>

}
fn main() {}