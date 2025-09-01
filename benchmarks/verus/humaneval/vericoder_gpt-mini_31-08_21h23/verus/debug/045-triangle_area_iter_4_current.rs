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
        // Work in mathematical/integer type to avoid overflow while reasoning
        let a_int: int = a as int;
        let q_int: int = q as int;
        let r_int: int = r as int;
        let h_int: int = h as int;
        // division remainder property for a = 2*q + r
        assert(a == 2 * q + r);
        assert(a_int == 2 * q_int + r_int);
        // multiply both sides by h
        assert(a_int * h_int == (2 * q_int + r_int) * h_int);
        // distribute multiplication
        assert((2 * q_int + r_int) * h_int == 2 * (q_int * h_int) + r_int * h_int);
        // divide by 2
        assert(a_int * h_int / 2 == 2 * (q_int * h_int) / 2 + r_int * h_int / 2);
        // simplify 2*x/2 == x for non-negative x
        assert(2 * (q_int * h_int) / 2 == q_int * h_int);
        // relate part1 and part2 to their integer counterparts
        assert((part1 as int) == q_int * h_int);
        assert((part2 as int) == r_int * h_int / 2);
        // combine
        assert((part1 as int) + (part2 as int) == q_int * h_int + r_int * h_int / 2);
        assert((part1 as int) + (part2 as int) == a_int * h_int / 2);
        // use the precondition to establish bounds for the cast back to u64
        assert(a_int * h_int / 2 <= (u64::MAX as int));
        assert((part1 as int) + (part2 as int) <= (u64::MAX as int));
        // finally, show the u64-level equality
        assert((area as int) == a_int * h_int / 2);
        assert(area == a * h / 2);
    }
    area
    // impl-end
}
// </vc-code>

fn main() {}
}