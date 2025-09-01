use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
            // a == 2 * a2
            assert(a128 == 2 * a2_128);
            // therefore (a * h) / 2 == a2 * h
            assert((a128 * h128) / 2 == a2_128 * h128);
            // from precondition: (a * h) / 2 <= u64::MAX
            // cast that fact to u128 to conclude the product fits into u64
            assert((a128 * h128) / 2 <= u64::MAX as u128);
            // hence a2 * h <= u64::MAX (in u128), so u64 multiplication won't overflow
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
            // a = 2*a2 + 1 and h = 2*h2 + (h % 2)
            // compute (a*h)/2 = (a2*h + h2) in u128
            // Expand a*h: (2*a2 + 1)*h = 2*a2*h + h
            // Divide by 2: (a*h)/2 = a2*h + h/2 = a2*h + h2
            assert(a128 * h128 / 2 == a2_128 * h128 + h2_128);
            // From precondition, (a*h)/2 <= u64::MAX, cast to u128
            assert(a128 * h128 / 2 <= u64::MAX as u128);
            // hence a2*h + h2 <= u64::MAX in u128, so addition and multiplication fit in u64
            assert(a2_128 * h128 + h2_128 <= u64::MAX as u128);
            // also each term is <= the sum, so individual multiplication fits
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