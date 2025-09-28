// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    a >= 0 && b >= a && x > 0
}

spec fn count_divisible_in_range(a: int, b: int, x: int) -> int
    recommends valid_input(a, b, x)
{
    if a == 0 {
        b / x + 1
    } else {
        b / x - (a - 1) / x
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): monotonicity of division */
proof fn div_monotone(m: int, n: int, x: int)
    requires
        x > 0,
        m <= n,
    ensures
        m / x <= n / x,
{
    let k = m / x;
    assert(k * x <= m);
    assert(m <= n);
    assert(k * x <= n);
    assert(k <= n / x);
}

/* helper modified by LLM (iteration 3): count non-negativity */
proof fn count_nonneg(a: int, b: int, x: int)
    requires
        valid_input(a, b, x),
    ensures
        count_divisible_in_range(a, b, x) >= 0,
{
    if a == 0 {
        assert(b >= 0);
        assert(x > 0);
        assert(b / x >= 0);
        assert(b / x + 1 >= 0);
    } else {
        assert(a > 0);
        assert(a - 1 <= b);
        div_monotone(a - 1, b, x);
        assert((a - 1) / x <= b / x);
        assert(b / x - (a - 1) / x >= 0);
    }
}

/* helper modified by LLM (iteration 3): relate i8 division to int division */
proof fn div_cast_eq(n: i8, d: i8)
    requires
        d > 0,
        n >= 0,
    ensures
        (n / d) as int == (n as int) / (d as int),
{
    let ni: int = n as int;
    let di: int = d as int;
    let k: int = (n / d) as int;
    assert(k * di <= ni);
    assert(ni < (k + 1) * di);
    assert(k == ni / di);
}

// </vc-helpers>

// <vc-spec>
fn count_divisible(a: i8, b: i8, x: i8) -> (count: i8)
    requires 
        valid_input(a as int, b as int, x as int),
    ensures 
        count as int == count_divisible_in_range(a as int, b as int, x as int),
        count >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): compute using i8 arithmetic and prove equivalence */
{
    let result: i8 = if a == 0_i8 {
        b / x + 1_i8
    } else {
        b / x - ((a - 1_i8) / x)
    };

    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        let xi: int = x as int;

        if a == 0_i8 {
            div_cast_eq(b, x);
            assert((b / x) as int == bi / xi);
            assert((1_i8) as int == 1);
            assert((result as int) == bi / xi + 1);
            assert(result as int == count_divisible_in_range(ai, bi, xi));
        } else {
            let am1: i8 = (a - 1_i8) as i8;
            div_cast_eq(b, x);
            div_cast_eq(am1, x);
            assert((b / x) as int == bi / xi);
            assert((am1 / x) as int == (ai - 1) / xi);
            assert((result as int) == bi / xi - (ai - 1) / xi);
            assert(result as int == count_divisible_in_range(ai, bi, xi));
        }

        count_nonneg(ai, bi, xi);
        assert(result >= 0_i8);
    }

    result
}

// </vc-code>


}

fn main() {}