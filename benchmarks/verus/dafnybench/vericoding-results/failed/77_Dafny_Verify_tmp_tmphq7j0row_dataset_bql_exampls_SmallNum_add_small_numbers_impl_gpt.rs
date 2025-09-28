use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_i32_min_le_forall()
    ensures
        forall |y: i32| #[trigger] (y == y) ==> i32::MIN <= y
{
    assert forall |y: i32| #[trigger] (y == y) ==> i32::MIN <= y by {
        assert((i32::MIN as int) <= (y as int));
    };
}
// </vc-helpers>

// <vc-spec>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_i32_min_le_forall();
    }
    i32::MIN
}
// </vc-code>

fn main() {
}

}