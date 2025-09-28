use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    assert(a.len() >= 8);
    assert(4 < a.len());
    assert(7 < a.len());

    let ghost pre = a@;

    let old4 = a[4];
    a[4] = old4 + 3;
    a[7] = 516;

    assert(a.len() == pre.len());
    assert(a@[4] == pre[4] + 3);
    assert(a@[7] == 516);
    assert(forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> #[trigger] a@[i] == pre[i]);
}
// </vc-code>

fn main() {}

}