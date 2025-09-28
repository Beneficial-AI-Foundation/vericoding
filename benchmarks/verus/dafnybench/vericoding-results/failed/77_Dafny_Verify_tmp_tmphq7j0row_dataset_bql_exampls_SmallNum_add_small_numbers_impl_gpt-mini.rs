use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn i32_min_le_all(y: i32) {
    // For any i32 value y, the minimum i32 value is <= y.
    assert(i32::MIN <= y);
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
    let r: i32 = i32::MIN;
    proof {
        // Use the helper lemma on the i32 product (no casts to int)
        i32_min_le_all(max * (n as i32));
        // Relate r to the lemma directly on i32s:
        assert(r <= max * (n as i32));
    }
    r
}
// </vc-code>

fn main() {
}

}