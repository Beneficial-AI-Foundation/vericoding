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
/* helper modified by LLM (iteration 5): monotonicity of division for positive divisor */
proof fn lemma_div_monotonic(a: int, b: int, x: int)
    requires
        x > 0,
        a <= b,
    ensures
        a / x <= b / x,
{
    assert(a / x <= b / x);
}

/* helper modified by LLM (iteration 5): non-negativity of the count function under valid_input */
proof fn lemma_count_nonneg(a: int, b: int, x: int)
    requires
        valid_input(a, b, x),
    ensures
        count_divisible_in_range(a, b, x) >= 0,
{
    if a == 0 {
        assert(count_divisible_in_range(a, b, x) == b / x + 1);
        assert(b >= 0);
        assert(x > 0);
        assert(b / x >= 0);
        assert(b / x + 1 >= 0);
    } else {
        assert(a >= 1);
        assert(a - 1 <= b);
        lemma_div_monotonic(a - 1, b, x);
        assert((a - 1) / x <= b / x);
        assert(b / x - (a - 1) / x >= 0);
        assert(count_divisible_in_range(a, b, x) == b / x - (a - 1) / x);
    }
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
{
    /* code modified by LLM (iteration 5): fix i8/int mismatches and provide proof of correctness and non-negativity */
    assert(x != 0i8);

    let res: i8 = if a == 0i8 {
        b / x + 1i8
    } else {
        let am1: i8 = a - 1i8;
        b / x - (am1 / x)
    };

    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        let xi: int = x as int;

        if a == 0i8 {
            assert((b / x) as int == bi / xi);
            assert(res as int == bi / xi + 1);
            assert(count_divisible_in_range(ai, bi, xi) == bi / xi + 1);
            assert(res as int == count_divisible_in_range(ai, bi, xi));
        } else {
            let am1: i8 = a - 1i8;
            assert(ai >= 1);
            assert((b / x) as int == bi / xi);
            assert((am1 / x) as int == (ai - 1) / xi);
            assert(res as int == bi / xi - ((ai - 1) / xi));
            assert(count_divisible_in_range(ai, bi, xi) == bi / xi - ((ai - 1) / xi));
            assert(res as int == count_divisible_in_range(ai, bi, xi));
        }

        lemma_count_nonneg(ai, bi, xi);
        assert(res as int >= 0);
        assert(res >= 0i8);
    }

    res
}
// </vc-code>


}

fn main() {}