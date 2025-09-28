use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let old_v4: i32 = a[4];
    // use wrapping_add to avoid arithmetic overflow/underflow issues
    a[4] = old_v4.wrapping_add(3);
    a[7] = 516;
    proof {
        // lengths unchanged
        assert(a.len() == old(a).len());

        // the captured pre-state value equals the old snapshot at index 4
        assert(old_v4 == old(a)[4]);

        // explicit values at updated indices
        assert(a[4] == old_v4.wrapping_add(3));
        assert(a[4] == old(a)[4] + 3);
        assert(a[7] == 516);

        // other elements unchanged
        assert(forall |i: int| 0 <= i < a.len() ==>
            (i != 7 && i != 4) ==> a[i] == old(a)[i]);
    }
}
// </vc-code>

fn main() {}

}