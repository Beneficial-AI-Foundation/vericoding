// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, c: int) -> bool {
    1 <= n <= 100 && 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn min_distance(n: int, a: int, b: int, c: int) -> int
    recommends valid_input(n, a, b, c)
{
    if n == 1 { 0 } else { (n - 1) * min(a, b) }
}

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove min(a,b) <= max(a, max(b,c)) */
proof fn min_le_max3(a: int, b: int, c: int)
    ensures
        min(a, b) <= max(a, max(b, c)),
{
    if a <= b {
        assert(min(a, b) == a);
        assert(a <= max(b, c));
        assert(min(a, b) <= max(a, max(b, c)));
    } else {
        assert(min(a, b) == b);
        assert(b <= max(b, c));
        assert(min(a, b) <= max(a, max(b, c)));
    }
}

/* helper modified by LLM (iteration 5): monotonicity of multiplication by non-negative */
proof fn mul_nonneg_monotone(k: int, x: int, y: int)
    requires
        k >= 0,
    ensures
        x <= y ==> k * x <= k * y,
{
    if x <= y {
        let d = y - x;
        assert(y == x + d);
        assert(d >= 0);
        assert(k * d >= 0);
        assert(k * y == k * x + k * d);
        assert(k * y - k * x == k * d);
        assert(k * y - k * x >= 0);
        assert(k * x <= k * y);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int)
    ensures 
        result >= 0,
        n == 1 ==> result == 0,
        result as int <= (n as int - 1) * max(a as int, max(b as int, c as int)),
        result as int == min_distance(n as int, a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result via int ghost and cast to i8, prove properties */
    let ni: int = n as int;
    let ai: int = a as int;
    let bi: int = b as int;
    let ci: int = c as int;

    let r_int: int = if ni == 1 { 0 } else { (ni - 1) * min(ai, bi) };

    proof {
        if ni == 1 {
            assert(r_int == 0);
            assert(min_distance(ni, ai, bi, ci) == 0);
            assert(r_int == min_distance(ni, ai, bi, ci));
            assert(r_int >= 0);
        } else {
            assert(r_int == (ni - 1) * min(ai, bi));
            assert(min_distance(ni, ai, bi, ci) == (ni - 1) * min(ai, bi));
            assert(r_int == min_distance(ni, ai, bi, ci));

            assert(ni - 1 >= 0);
            min_le_max3(ai, bi, ci);
            mul_nonneg_monotone(ni - 1, min(ai, bi), max(ai, max(bi, ci)));
            assert((ni - 1) * min(ai, bi) <= (ni - 1) * max(ai, max(bi, ci)));
            assert(r_int <= (ni - 1) * max(ai, max(bi, ci)));
            assert(r_int >= 0);
        }
    }

    let result: i8 = r_int as i8;
    result
}

// </vc-code>


}

fn main() {}