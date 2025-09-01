use vstd::prelude::*;

verus! {

// <vc-helpers>
fn div_mul2(z: u64) {
    ensures (2 * z) / 2 == z;
} proof {
    // (2*z)/2 == z holds for integer division
    assert((2 * z) / 2 == z);
}

fn div_mul2_plus_one(z: u64) {
    ensures (2 * z + 1) / 2 == z;
} proof {
    // (2*z+1)/2 == z holds for integer division (floor)
    assert((2 * z + 1) / 2 == z);
}

fn div2_add_even(u: u64, v: u64)
    requires u % 2 == 0
    ensures (u + v) / 2 == u / 2 + v / 2
{
} proof {
    let k: u64 = u / 2;
    assert(u == 2 * k);
    let m: u64 = v / 2;
    let s: u64 = v % 2;
    assert(v == 2 * m + s);
    assert(s == 0 || s == 1);

    let sum: u64 = k + m;
    if s == 0 {
        // (u+v)/2 == (2*sum)/2 == sum
        assert((u + v) / 2 == (2 * sum) / 2);
        div_mul2(sum);
        assert((u + v) / 2 == sum);
    } else {
        // s == 1
        // (u+v)/2 == (2*sum + 1)/2 == sum
        assert((u + v) / 2 == (2 * sum + 1) / 2);
        div_mul2_plus_one(sum);
        assert((u + v) / 2 == sum);
    }

    assert(sum == u / 2 + v / 2);
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
    let q: u64 = a / 2;
    let r: u64 = a % 2;
    proof {
        // a = 2*q + r, with r in {0,1}
        assert(a == 2 * q + r);
        assert(r == 0 || r == 1);

        // derive identity a*h/2 == q*h + (r*h)/2
        // a*h = 2*q*h + r*h
        assert(a * h == 2 * q * h + r * h);
        // (2*q*h) is even, so we can split the division
        div2_add_even(2 * q * h, r * h);
        // from lemma: (2*q*h + r*h)/2 == (2*q*h)/2 + (r*h)/2
        // and (2*q*h)/2 == q*h
        div_mul2(q * h);
        assert((a * h) / 2 == q * h + (r * h) / 2);

        // from that, q*h <= a*h/2 because (r*h)/2 >= 0
        assert((r * h) / 2 >= 0);
        assert(q * h <= q * h + (r * h) / 2);
        assert(q * h <= a * h / 2);
    }

    let part1: u64 = q * h;
    let part2: u64 = (r * h) / 2;
    let area: u64 = part1 + part2;

    proof {
        // verify the result equals a * h / 2
        assert(area == (q * h) + (r * h) / 2);
        assert(area == a * h / 2);
    }

    area
    // impl-end
}
// </vc-code>

fn main() {}
}