use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added no helpers; proofs are self-contained in the implementation.
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
    if a % 2 == 0 {
        let a2: u64 = a / 2;
        proof {
            // Work in u128 to avoid overflow in intermediate reasoning
            let a128: u128 = a as u128;
            let h128: u128 = h as u128;
            let a2_128: u128 = a2 as u128;
            // remainder when dividing a by 2
            let r: u128 = a128 % 2;
            // since a is even, remainder is 0
            assert(r == 0);
            // express a as 2*a2 + r (here r == 0)
            assert(a128 == 2 * a2_128 + r);
            // multiply both sides by h
            assert(a128 * h128 == (2 * a2_128 + r) * h128);
            // expand the right-hand side
            assert(a128 * h128 == 2 * a2_128 * h128 + r * h128);
            // since r == 0, the last term vanishes
            assert(a128 * h128 == 2 * a2_128 * h128);
            // dividing both sides by 2 yields the desired equality
            assert((a128 * h128) / 2 == (2 * a2_128 * h128) / 2);
            assert((2 * a2_128 * h128) / 2 == a2_128 * h128);
            // from precondition: (a * h) / 2 <= u64::MAX
            assert((a128 * h128) / 2 <= u64::MAX as u128);
            // hence a2 * h fits in u64
            assert(a2_128 * h128 <= u64::MAX as u128);
        }
        let area: u64 = a2 * h;
        area
    } else {
        let a2: u64 = a / 2;
        let h2: u64 = h / 2;
        proof {
            // Use u128 for safe intermediate arithmetic
            let a128: u128 = a as u128;
            let h128: u128 = h as u128;
            let a2_128: u128 = a2 as u128;
            let h2_128: u128 = h2 as u128;
            // express a and h in terms of their halves and remainders
            let ra: u128 = a128 % 2;
            let rh: u128 = h128 % 2;
            assert(ra == 1); // a is odd
            assert(a128 == 2 * a2_128 + ra);
            assert(h128 == 2 * h2_128 + rh);
            assert(rh < 2);
            // expand a*h
            assert(a128 * h128 == (2 * a2_128 + ra) * (2 * h2_128 + rh));
            assert(a128 * h128 == 4 * a2_128 * h2_128 + 2 * a2_128 * rh + 2 * h2_128 + ra * rh);
            // divide by 2
            assert((a128 * h128) / 2 == (4 * a2_128 * h2_128 + 2 * a2_128 * rh + 2 * h2_128 + ra * rh) / 2);
            // simplify term-wise: each term divisible by 2 except (ra * rh)
            // compute floor division: (4*x)/2 = 2*x, (2*y)/2 = y
            assert((4 * a2_128 * h2_128) / 2 == 2 * a2_128 * h2_128);
            assert((2 * a2_128 * rh) / 2 == a2_128 * rh);
            assert((2 * h2_128) / 2 == h2_128);
            // combine the simplified parts
            assert((a128 * h128) / 2 == 2 * a2_128 * h2_128 + a2_128 * rh + h2_128 + (ra * rh) / 2);
            // note ra == 1, so (ra * rh) / 2 == rh / 2
            assert(ra == 1);
            assert((ra * rh) / 2 == rh / 2);
            // but rh is 0 or 1, so rh / 2 == 0
            assert(rh < 2);
            assert(rh / 2 == 0);
            // therefore (a*h)/2 == 2*a2*h2 + a2*rh + h2
            assert((a128 * h128) / 2 == 2 * a2_128 * h2_128 + a2_128 * rh + h2_128);
            // and 2*a2*h2 + a2*rh == a2*(2*h2 + rh) == a2*h
            assert(2 * a2_128 * h2_128 + a2_128 * rh == a2_128 * (2 * h2_128 + rh));
            assert(a2_128 * (2 * h2_128 + rh) == a2_128 * h128);
            // combine to get (a*h)/2 == a2*h + h2
            assert((a128 * h128) / 2 == a2_128 * h128 + h2_128);
            // from precondition, (a*h)/2 <= u64::MAX
            assert((a128 * h128) / 2 <= u64::MAX as u128);
            // hence a2*h + h2 fits in u64
            assert(a2_128 * h128 + h2_128 <= u64::MAX as u128);
            assert(a2_128 * h128 <= u64::MAX as u128);
        }
        let area: u64 = a2 * h + h2;
        area
    }
    // impl-end
}
// </vc-code>

fn main() {}
}