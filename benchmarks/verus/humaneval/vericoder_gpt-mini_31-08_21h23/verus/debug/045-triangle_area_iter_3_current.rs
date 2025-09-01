use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let q: u64 = a / 2;
    let r: u64 = a % 2;
    let part1: u64 = q * h;
    let part2: u64 = (r * h) / 2;
    let area: u64 = part1 + part2;
    proof {
        // Work in a larger integer type to avoid overflow while reasoning
        let a128: u128 = a as u128;
        let q128: u128 = q as u128;
        let r128: u128 = r as u128;
        let h128: u128 = h as u128;
        // division remainder property for a = 2*q + r
        assert(a == 2 * q + r);
        assert(a128 == 2u128 * q128 + r128);
        // multiply both sides by h
        assert(a128 * h128 == (2u128 * q128 + r128) * h128);
        // distribute multiplication
        assert((2u128 * q128 + r128) * h128 == 2u128 * (q128 * h128) + r128 * h128);
        // divide by 2
        assert(a128 * h128 / 2u128 == 2u128 * (q128 * h128) / 2u128 + r128 * h128 / 2u128);
        // simplify 2*x/2 == x
        assert(2u128 * (q128 * h128) / 2u128 == q128 * h128);
        // relate part1 and part2 to their u128 counterparts
        assert((part1 as u128) == q128 * h128);
        assert((part2 as u128) == r128 * h128 / 2u128);
        // combine
        assert((part1 as u128) + (part2 as u128) == q128 * h128 + r128 * h128 / 2u128);
        assert((part1 as u128) + (part2 as u128) == a128 * h128 / 2u128);
        // use the precondition to establish bounds for the cast back to u64
        assert(a128 * h128 / 2u128 <= (u64::MAX as u128));
        assert((part1 as u128) + (part2 as u128) <= (u64::MAX as u128));
        // finally, show the u64-level equality
        assert((area as u128) == a128 * h128 / 2u128);
        assert(area == a * h / 2);
    }
    area
    // impl-end
}
// </vc-code>

fn main() {}
}