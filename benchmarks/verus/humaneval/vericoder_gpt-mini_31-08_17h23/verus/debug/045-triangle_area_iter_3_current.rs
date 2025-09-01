use vstd::prelude::*;

verus! {

// <vc-helpers>
fn div2_double_u128(x: u128)
    ensures ( (2 * x) / 2 == x )
{
    proof {
        // trivial arithmetic identity for integers
        assert((2 * x) / 2 == x);
    }
}

fn div4_double_u128(x: u128)
    ensures ( (4 * x) / 2 == 2 * x )
{
    proof {
        assert((4 * x) / 2 == 2 * x);
    }
}

fn div2_split_u128(X: u128, Y: u128)
    requires Y < 2
    ensures ( (2 * X + Y) / 2 == X + Y / 2 )
{
    proof {
        // straightforward division identity when splitting off a factor 2
        assert((2 * X + Y) / 2 == X + Y / 2);
    }
}

fn small_div2_zero(y: u128)
    requires y < 2
    ensures ( y / 2 == 0 )
{
    proof {
        assert(y / 2 == 0);
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
            // dividing both sides by 2 yields the desired equality using lemma
            div2_double_u128(a2_128 * h128);
            assert((a128 * h128) / 2 == a2_128 * h128);
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
            // expand a*h correctly: (2*a2 + ra)*(2*h2 + rh)
            assert(a128 * h128 == (2 * a2_128 + ra) * (2 * h2_128 + rh));
            assert(a128 * h128 == 4 * a2_128 * h2_128 + 2 * a2_128 * rh + 2 * ra * h2_128 + ra * rh);
            // group as 2*X + Y where X = 2*a2*h2 + a2*rh + ra*h2 and Y = ra*rh
            let X: u128 = 2 * a2_128 * h2_128 + a2_128 * rh + ra * h2_128;
            let Y: u128 = ra * rh;
            assert(a128 * h128 == 2 * X + Y);
            // divide by 2 using splitting lemma (Y < 2 since ra in {0,1} and rh in {0,1})
            assert(Y < 2);
            div2_split_u128(X, Y);
            assert((a128 * h128) / 2 == X + Y / 2);
            // ra == 1, so Y = rh, and Y/2 == rh/2
            assert(ra == 1);
            assert(Y == ra * rh);
            assert(Y == rh);
            // rh < 2 so rh / 2 == 0
            small_div2_zero(rh);
            assert(rh / 2 == 0);
            // therefore (a*h)/2 == X
            assert((a128 * h128) / 2 == X);
            // simplify X to a2*h + h2:
            // X = 2*a2*h2 + a2*rh + ra*h2
            // with ra == 1, X = 2*a2*h2 + a2*rh + h2 = a2*(2*h2 + rh) + h2 = a2*h + h2
            assert(2 * a2_128 * h2_128 + a2_128 * rh + ra * h2_128 == a2_128 * (2 * h2_128 + rh) + h2_128);
            assert(a2_128 * (2 * h2_128 + rh) + h2_128 == a2_128 * h128 + h2_128);
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