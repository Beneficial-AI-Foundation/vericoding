use vstd::prelude::*;

verus! {

// <vc-helpers>
const MAX_SAFE_SIZE: i32 = 18918;

proof fn lemma_mul_is_safe(size: i32)
    requires 0 < size <= MAX_SAFE_SIZE
    ensures 6 * size * size <= i32::MAX
{
    let max_area = 6 * MAX_SAFE_SIZE * MAX_SAFE_SIZE;
    assert(max_area == 2147483544);
    assert(2147483544 <= i32::MAX);
    assert(size * size <= MAX_SAFE_SIZE * MAX_SAFE_SIZE) by {
        let diff = MAX_SAFE_SIZE - size;
        assert(diff >= 0);
        assert(MAX_SAFE_SIZE * MAX_SAFE_SIZE - size * size == diff * (MAX_SAFE_SIZE + size));
        assert(diff * (MAX_SAFE_SIZE + size) >= 0);
    }
    assert(6 * size * size <= 6 * MAX_SAFE_SIZE * MAX_SAFE_SIZE);
}
// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    requires(size > 0 && size <= MAX_SAFE_SIZE);
    proof {
        lemma_mul_is_safe(size);
    }
    let area = (6 * (size as i64) * (size as i64)) as i32;
    area
}
// </vc-code>

fn main() {
}

}