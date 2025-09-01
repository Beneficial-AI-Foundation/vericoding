use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helpers section remains empty as no updates are needed for fixing the verification errors.
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
        assert(a * h / 2 <= u64::MAX);
    }
    let product = (a as u128) * (h as u128);
    let area_u128 = product / 2;
    proof {
        assert(product as int == (a as int) * (h as int));
        assert(area_u128 as int == (a as int) * (h as int) / 2);
        assert(area_u128 <= u64::MAX as u128);
    }
    let area = area_u128 as u64;
    proof {
        assert(area as int == (a as int) * (h as int) / 2);
    }
    area
}
// </vc-code>

fn main() {}
}