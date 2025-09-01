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
    // impl-start
    proof {
        assert(a * h / 2 <= u64::MAX);
        assert(a <= u64::MAX);
        assert(h <= u64::MAX);
        assert(a * h <= u64::MAX) by {
            assert(a * h / 2 <= u64::MAX);
            assert(a * h / 2 * 2 == a * h);
            assert(a * h <= u64::MAX);
        };
    }
    let product = a * h;
    let area = product / 2;
    area
    // impl-end
}
// </vc-code>

fn main() {}
}