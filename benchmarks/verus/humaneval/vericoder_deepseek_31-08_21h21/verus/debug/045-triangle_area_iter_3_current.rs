use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mul_div_le_lemma(a: u64, h: u64)
    requires
        a > 0,
        h > 0,
    ensures
        a * h / 2 <= a * h,
{
    assert(a >= 1 && h >= 1);
    assert(a * h >= 1);
}

proof fn triangle_area_valid_lemma(a: u64, h: u64)
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX,
    ensures
        a * h <= u64::MAX,
{
    mul_div_le_lemma(a, h);
    assert(a * h / 2 <= u64::MAX);
    assert(a * h / 2 <= a * h);
    
    if (a * h > u64::MAX) {
        assert(a * h / 2 <= u64::MAX < a * h);
        assert(a * h / 2 < a * h);
        assert(false);
    }
}
// </vc-helpers>

// <vc-spec>
fn triangle_area(a: u64, h: u64) -> (area: u64)
    // pre-conditions-start
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,
    // pre-conditions-end
    // post-conditions-start
    ensures
        area == a * h / 2,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    proof {
        triangle_area_valid_lemma(a, h);
        assert(a * h <= u64::MAX);
    }
    let area = a * h / 2;
    area
}
// </vc-code>

fn main() {}
}