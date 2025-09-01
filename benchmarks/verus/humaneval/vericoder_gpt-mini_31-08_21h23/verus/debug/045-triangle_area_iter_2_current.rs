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
    let q: u64 = a / 2;
    let r: u64 = a % 2;
    if r == 0 {
        proof {
            // r == 0 => a == 2*q
            assert(a == 2 * q + r);
            assert(r == 0);
            assert(a == 2 * q);
            // multiply by h: a*h == 2*(q*h)
            assert(a * h == 2 * (q * h));
            // divide by 2: a*h/2 == q*h
            assert(a * h / 2 == (2 * (q * h)) / 2);
            assert((2 * (q * h)) / 2 == q * h);
            assert(a * h / 2 == q * h);
            // bounds
            assert(a * h / 2 <= u64::MAX);
            assert(q * h == a * h / 2);
            assert(q * h <= u64::MAX);
        }
        let area: u64 = q * h;
        proof {
            assert(area == q * h);
            assert(q * h == a * h / 2);
            assert(area == a * h / 2);
        }
        area
    } else {
        proof {
            // r == 1 => a == 2*q + 1
            assert(a == 2 * q + r);
            assert(r == 1);
            // multiply: a*h == 2*(q*h) + h
            assert(a * h == (2 * q + r) * h);
            assert((2 * q + r) * h == (2 * q) * h + r * h);
            assert((2 * q) * h == 2 * (q * h));
            assert(r * h == h);
            assert(a * h == 2 * (q * h) + h);
            // divide by 2: a*h/2 == q*h + h/2
            assert(a * h / 2 == (2 * (q * h) + h) / 2);
            assert((2 * (q * h) + h) / 2 == q * h + (h / 2));
            assert(a * h / 2 == q * h + (h / 2));
            // each component <= sum, and sum <= MAX
            assert(q * h <= q * h + (h / 2));
            assert(h / 2 <= q * h + (h / 2));
            assert(q * h + (h / 2) == a * h / 2);
            assert(a * h / 2 <= u64::MAX);
            assert(q * h <= u64::MAX);
            assert(h / 2 <= u64::MAX);
        }
        let part1: u64 = q * h;
        let part2: u64 = h / 2;
        let area: u64 = part1 + part2;
        proof {
            assert(part1 == q * h);
            assert(part2 == h / 2);
            assert(part1 + part2 == q * h + (h / 2));
            assert(q * h + (h / 2) == a * h / 2);
            assert(part1 + part2 == a * h / 2);
        }
        area
    }
    // impl-end
}
// </vc-code>

fn main() {}
}