use vstd::prelude::*;

verus! {

// <vc-helpers>
fn div_mul2(z: u64)
    ensures (2u64 * z) / 2u64 == z
{
    proof {
        // (2*z)/2 == z holds for integer division
        assert((2u64 * z) / 2u64 == z);
    }
}

fn div_mul2_plus_one(z: u64)
    ensures (2u64 * z + 1u64) / 2u64 == z
{
    proof {
        // (2*z+1)/2 == z holds for integer division (floor)
        assert((2u64 * z + 1u64) / 2u64 == z);
    }
}

fn div2_add_even(u: u64, v: u64)
    requires u % 2u64 == 0u64
    ensures (u + v) / 2u64 == u / 2u64 + v / 2u64
{
    proof {
        let k: u64 = u / 2u64;
        assert(u == 2u64 * k);
        let m: u64 = v / 2u64;
        let s: u64 = v % 2u64;
        assert(v == 2u64 * m + s);
        assert(s == 0u64 || s == 1u64);

        let sum: u64 = k + m;
        if s == 0u64 {
            // (u+v)/2 == (2*sum)/2 == sum
            assert((u + v) / 2u64 == (2u64 * sum) / 2u64);
            div_mul2(sum);
            assert((u + v) / 2u64 == sum);
        } else {
            // s == 1
            // (u+v)/2 == (2*sum + 1)/2 == sum
            assert((u + v) / 2u64 == (2u64 * sum + 1u64) / 2u64);
            div_mul2_plus_one(sum);
            assert((u + v) / 2u64 == sum);
        }

        assert(sum == u / 2u64 + v / 2u64);
    }
}
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
    let q: u64 = a / 2u64;
    let r: u64 = a % 2u64;
    proof {
        // a = 2*q + r, with r in {0,1}
        assert(a == 2u64 * q + r);
        assert(r == 0u64 || r == 1u64);

        // derive identity a*h/2 == q*h + (r*h)/2
        // a*h = 2*q*h + r*h
        assert(a * h == 2u64 * q * h + r * h);
        // (2*q*h) is even, so we can split the division
        div2_add_even(2u64 * q * h, r * h);
        // from lemma: (2*q*h + r*h)/2 == (2*q*h)/2 + (r*h)/2
        // and (2*q*h)/2 == q*h
        div_mul2(q * h);
        assert((a * h) / 2u64 == q * h + (r * h) / 2u64);

        // from that, q*h <= a*h/2 because (r*h)/2 >= 0
        assert((r * h) / 2u64 >= 0u64);
        assert(q * h <= q * h + (r * h) / 2u64);
        assert(q * h <= a * h / 2u64);
    }

    let part1: u64 = q * h;
    let part2: u64 = (r * h) / 2u64;
    let area: u64 = part1 + part2;

    proof {
        // verify the result equals a * h / 2
        assert(area == (q * h) + (r * h) / 2u64);
        assert(area == a * h / 2u64);
    }

    area
    // impl-end
}
// </vc-code>

fn main() {}
}