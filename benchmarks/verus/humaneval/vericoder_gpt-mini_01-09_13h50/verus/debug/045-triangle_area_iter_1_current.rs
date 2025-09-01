use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    proof {
        // a = 2*q + r, with r in {0,1}
        assert(a == 2 * q + r);
        assert(r == 0 || r == 1);

        // q * h <= a * h / 2
        // q <= a / 2, so q * h <= (a / 2) * h = a * h / 2
        assert(q * h <= a * h / 2);

        // r * (h/2) <= a * h / 2
        if r == 0 {
            assert(r * (h / 2) == 0);
        } else {
            // r == 1 and a > 0 implies a >= 1, so h/2 <= a * h / 2
            assert(a >= 1);
            assert(h / 2 <= a * h / 2);
            assert(r * (h / 2) == h / 2);
        }

        // From precondition a * h / 2 <= u64::MAX, both parts are <= u64::MAX
        assert(a * h / 2 <= u64::MAX);
        assert(q * h <= u64::MAX);
        assert(r * (h / 2) <= u64::MAX);

        // identity: a*h/2 == q*h + r*(h/2)
        assert(a * h == 2 * q * h + r * h);
        assert(a * h / 2 == q * h + r * h / 2);
        assert(r * h / 2 == r * (h / 2));
        assert(a * h / 2 == q * h + r * (h / 2));
    }

    let part1: u64 = q * h;
    let part2: u64 = r * (h / 2);
    let area: u64 = part1 + part2;

    proof {
        // verify the result equals a * h / 2
        assert(area == (q * h) + (r * (h / 2)));
        assert(area == a * h / 2);
    }

    area
    // impl-end
}
// </vc-code>

fn main() {}
}