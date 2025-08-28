use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn safe_add(x: i32, y: i32) -> bool {
    x as int + y as int <= i32::MAX as int && x as int + y as int >= i32::MIN as int
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let old_val = a[4];
    a.set(4, old_val + 3);
    a.set(7, 516);
}
// </vc-code>

fn main() {}

}