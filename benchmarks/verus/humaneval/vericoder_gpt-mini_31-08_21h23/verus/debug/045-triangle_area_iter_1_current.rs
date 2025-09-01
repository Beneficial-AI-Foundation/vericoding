use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
fn div2_mul_decomp(a: u64, h: u64)
    ensures (a / 2) * h + (a % 2) * (h / 2) == a * h / 2
{
    proof {
        let q = a / 2;
        let r = a % 2;
        // a == 2*q + r
        assert(a == 2 * q + r);
        // multiply both sides by h
        assert(a * h == (2 * q + r) * h);
        // distribute
        assert((2 * q + r) * h == (2 * q) * h + r * h);
        assert((2 * q) * h == 2 * (q * h));
        // combine
        assert(a * h == 2 * (q * h) + r * h);
        // divide by 2
        assert(a * h / 2 == (2 * (q * h) + r * h) / 2);
        // (2*x + y)/2 == x + y/2
        assert((2 * (q * h) + r * h) / 2 == q * h + (r * h) / 2);
        // handle r = 0 or 1
        if r == 0 {
            assert((r * h) / 2 == 0);
            assert(r * (h / 2) == 0);
        } else {
            assert(r == 1);
            assert((r * h) / 2 == h / 2);
            assert(r * (h / 2) == h / 2);
        }
        assert((r * h) / 2 == r * (h / 2));
        assert(q * h + (r * h) / 2 == q * h + r * (h / 2));
        assert(q * h + r * (h / 2) == (a / 2) * h + (a % 2) * (h / 2));
        assert((a / 2) * h + (a % 2) * (h / 2) == a * h / 2);
    }
}
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
    if r == 0 {
        proof {
            // decompose to relate q*h with a*h/2
            div2_mul_decomp(a, h);
            // from lemma: q*h + 0 == a*h/2, so q*h <= a*h/2 <= u64::MAX
            assert((q * h) <= a * h / 2);
            assert(a * h / 2 <= u64::MAX);
            assert((q * h) <= u64::MAX);
        }
        let area: u64 = q * h;
        proof {
            div2_mul_decomp(a, h);
            assert(area == a * h / 2);
        }
        area
    } else {
        proof {
            // decompose to relate q*h + (h/2) with a*h/2
            div2_mul_decomp(a, h);
            // from lemma: q*h + (h/2) == a*h/2, so sum <= u64::MAX
            assert((q * h) + (h / 2) <= a * h / 2);
            assert(a * h / 2 <= u64::MAX);
            assert((q * h) + (h / 2) <= u64::MAX);
            // hence each component is <= MAX
            assert((q * h) <= u64::MAX);
            assert((h / 2) <= u64::MAX);
        }
        let part1: u64 = q * h;
        let part2: u64 = h / 2;
        let area: u64 = part1 + part2;
        proof {
            div2_mul_decomp(a, h);
            assert(part1 + part2 == a * h / 2);
        }
        area
    }
    // impl-end
}
// </vc-code>

fn main() {}
}