use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let product = (a as u128) * (h as u128);
    let area = (product / 2) as u64;
    proof {
        assert(product == a * h);
        assert((product / 2) == (a * h) / 2);
        assert((product / 2) <= u64::MAX);
        assert(area == (product / 2) as u64);
    }
    area
}
// </vc-code>

fn main() {}
}