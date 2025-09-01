use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// (no helpers needed)
 // </vc-helpers>
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
    // do intermediate arithmetic in u128 to avoid u64 overflow
    let part1_128: u128 = (q as u128) * (h as u128);
    let part2_128: u128 = ((r as u128) * (h as u128)) / 2u128;
    let area_128: u128 = part1_128 + part2_128;
    proof {
        // relate a, q, r: a = 2*q + r
        assert(a == 2 * q + r);
        // lift to u128 and multiply by h
        assert((a as u128) == 2u128 * (q as u128) + (r as u128));
        assert(((a as u128) * (h as u128)) == (2u128 * (q as u128) + (r as u128)) * (h as u128));
        // distribute
        assert(((2u128 * (q as u128) + (r as u128)) * (h as u128)) == 2u128 * ((q as u128) * (h as u128)) + (r as u128) * (h as u128));
        // divide by 2
        assert(((a as u128) * (h as u128)) / 2u128 == (2u128 * ((q as u128) * (h as u128)) + (r as u128) * (h as u128)) / 2u128);
        // simplify 2*x/2 == x
        assert((2u128 * ((q as u128) * (h as u128))) / 2u128 == (q as u128) * (h as u128));
        // identify parts
        assert(part1_128 == (q as u128) * (h as u128));
        assert(part2_128 == ((r as u128) * (h as u128)) / 2u128);
        // combine equality
        assert(part1_128 + part2_128 == ((a as u128) * (h as u128)) / 2u128);
        // use precondition a*h/2 <= u64::MAX to bound area_128
        assert(((a as u128) * (h as u128)) / 2u128 <= (u64::MAX as u128));
        assert(area_128 <= (u64::MAX as u128));
    }
    // safe to cast down to u64 now
    let area: u64 = area_128 as u64;
    proof {
        // show numeric equality at mathematical level
        let a_int: int = a as int;
        let h_int: int = h as int;
        let area_int: int = area as int;
        assert(area_int == (a_int * h_int) / 2);
        // conclude u64-level equality (the verifier accepts this conversion reasoning)
        assert(area == a * h / 2);
    }
    area
    // impl-end
}
// </vc-code>

fn main() {}
}