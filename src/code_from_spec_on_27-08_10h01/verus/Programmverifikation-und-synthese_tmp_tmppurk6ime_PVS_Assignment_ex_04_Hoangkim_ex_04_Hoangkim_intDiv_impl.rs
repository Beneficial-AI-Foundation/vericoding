use vstd::prelude::*;

verus! {

//Problem 01

//problem02
//a)

// <vc-helpers>
spec fn div_quotient(n: int, d: int) -> int
    recommends n >= 0, d > 0
{
    n / d
}

spec fn div_remainder(n: int, d: int) -> int
    recommends n >= 0, d > 0
{
    n % d
}

proof fn division_properties(n: int, d: int)
    requires n >= 0, d > 0
    ensures n == d * (n / d) + (n % d)
    ensures 0 <= n % d < d
{
}

proof fn quotient_bound_lemma(n: int, d: int)
    requires n >= d, n >= 0, d > 0
    ensures n / d <= n / 2
{
    if d >= 2 {
        assert(n / d <= n / 2);
    } else {
        assert(d == 1);
        assert(n / d == n);
        assert(n >= d);
        assert(n >= 1);
        if n == 1 {
            assert(n / d == 1 && n / 2 == 0);
            assert(false);
        } else {
            assert(n >= 2);
            assert(n / 2 >= 1);
            assert(n <= n / 2 * 2);
            if n % 2 == 0 {
                assert(n == n / 2 * 2);
                assert(n / 2 < n);
                assert(false);
            } else {
                assert(n == n / 2 * 2 + 1);
                assert(n / 2 < n);
                assert(false);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn int_div(n: int, d: int) -> (result: (int, int))
    requires n >= d && n >= 0 && d > 0,
    ensures ({
        let (q, r) = result;
        (d * q) + r == n && 0 <= q <= n / 2 && 0 <= r < d
    })
// </vc-spec>
// </vc-spec>

// <vc-code>
proof fn int_div(n: int, d: int) -> (result: (int, int))
    requires n >= d && n >= 0 && d > 0
    ensures ({
        let (q, r) = result;
        (d * q) + r == n && 0 <= q <= n / 2 && 0 <= r < d
    })
{
    let q = n / d;
    let r = n % d;
    
    proof {
        division_properties(n, d);
        assert((d * q) + r == n);
        assert(0 <= r < d);
        assert(0 <= q);
        
        if d == 1 {
            assert(q == n);
            assert(n >= d);
            assert(n >= 1);
            assert(false);
        } else {
            assert(d >= 2);
            assert(q <= n / 2) by {
                assert(n == d * q + r);
                assert(r >= 0);
                assert(d * q <= n);
                assert(q <= n / d);
                assert(d >= 2);
                assert(n / d <= n / 2);
            }
        }
    }
    
    (q, r)
}
// </vc-code>

fn main() {
}

}