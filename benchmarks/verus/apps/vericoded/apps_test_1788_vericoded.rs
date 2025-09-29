// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    -100 <= a <= 100 && -100 <= b <= 100 && (a + b) % 2 == 0 && (a - b) % 2 == 0
}

spec fn correct_solution(a: int, b: int, x: int, y: int) -> bool {
    a == x + y && b == x - y
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): half_bounds lemma */
proof fn half_bounds(n: int)
    requires
        -200 <= n <= 200,
        n % 2 == 0,
    ensures
        -100 <= n/2 <= 100,
{
    let m = n/2;
    assert(n == 2*m);
    assert(-100 <= m && m <= 100);
}

/* helper modified by LLM (iteration 4): int to i8 roundtrip lemma */
proof fn int_roundtrip_i8(v: int)
    requires
        -128 <= v <= 127,
    ensures
        (v as i8) as int == v,
{
    let w: i8 = v as i8;
    assert((w as int) == v);
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int)
    ensures correct_solution(a as int, b as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): compute x,y as (a+b)/2 and (a-b)/2 with proofs */
{
    let s16: i16 = (a as i16) + (b as i16);
    let d16: i16 = (a as i16) - (b as i16);
    let x: i8 = (s16 / 2) as i8;
    let y: i8 = (d16 / 2) as i8;

    proof {
        let ai = a as int;
        let bi = b as int;
        let s = ai + bi;
        let d = ai - bi;
        assert(valid_input(ai, bi));
        assert(-100 <= ai && ai <= 100);
        assert(-100 <= bi && bi <= 100);
        assert((ai + bi) % 2 == 0);
        assert((ai - bi) % 2 == 0);
        assert((s16 as int) == s);
        assert((d16 as int) == d);
        half_bounds(s);
        half_bounds(d);
        let xi_int = s / 2;
        let yi_int = d / 2;
        int_roundtrip_i8(xi_int);
        int_roundtrip_i8(yi_int);
        assert((x as int) == xi_int);
        assert((y as int) == yi_int);
        assert(ai == (x as int) + (y as int));
        assert(bi == (x as int) - (y as int));
    }

    (x, y)
}

// </vc-code>


}

fn main() {}