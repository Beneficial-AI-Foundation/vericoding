// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use int types to avoid usize/int mismatch */
fn div_to_mul(a: int, n: int)
    requires
        a > 0,
        a <= n / a,
    ensures
        a * a <= n,
{
    proof {
        // (n / a) * a <= n holds for integer division
        assert((n / a) * a <= n);
        // multiply both sides of a <= n / a by a (> 0)
        assert(a * a <= (n / a) * a);
        assert(a * a <= n);
    }
}

/* helper modified by LLM (iteration 2): use int types to avoid usize/int mismatch */
fn not_div_implies_mul_gt(a: int, n: int)
    requires
        a > 0,
        !(a <= n / a),
    ensures
        n < a * a,
{
    proof {
        // a > n / a
        assert(a > n / a);
        // multiply both sides by a (> 0)
        assert(a * a > (n / a) * a);
        // (n / a) * a <= n
        assert((n / a) * a <= n);
        assert(a * a > n);
    }
}

// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use int r and call int helpers, cast final result to usize */
{
    let mut r: int = 0;
    while (r + 1) <= (n as int) / (r + 1)
        invariant
            r <= n as int,
            r * r <= n as int,
        decreases (n as int) - r
    {
        let a = r + 1;
        r = r + 1;
        proof {
            // r == a now
            assert(r == a);
            assert(a <= (n as int) / a);
            assert(r > 0);
            div_to_mul(r, n as int);
            assert(r * r <= n as int);
            // for r >= 1 we have r <= r * r, so r <= n follows
            assert(r <= r * r);
            assert(r <= n as int);
        }
    }
    // After loop, the condition is false: !(r+1 <= n/(r+1)), so (r+1)*(r+1) > n
    proof {
        let a = r + 1;
        assert(!(a <= (n as int) / a));
        not_div_implies_mul_gt(a, n as int);
    }
    (r as usize)
}

// </vc-code>

}
fn main() {}