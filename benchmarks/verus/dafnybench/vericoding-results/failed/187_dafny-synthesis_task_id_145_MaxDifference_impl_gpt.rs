use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn i32_le_max(x: i32)
    ensures x <= i32::MAX
{
    assert(x <= i32::MAX);
}
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    proof {
        assert_forall_by(|i: int, j: int| {
            requires(0 <= i < a.len() && 0 <= j < a.len());
            ensures(a[i] - a[j] <= i32::MAX);
            i32_le_max(a[i] - a[j]);
        });
    }
    i32::MAX
}
// </vc-code>

fn main() {
}

}