// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 12 && 1 <= b <= 31
}

spec fn takahashi_count(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if a > b { a - 1 } else { a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma proving bounds of takahashi_count */
proof fn lemma_count_bounds(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        0 <= takahashi_count(a, b),
        takahashi_count(a, b) <= 12,
{
    reveal(takahashi_count);
    if a > b {
        assert(takahashi_count(a, b) == a - 1);
        assert(1 <= a && a <= 12);
        assert(0 <= a - 1 && a - 1 <= 11);
        assert(0 <= takahashi_count(a, b) && takahashi_count(a, b) <= 12);
    } else {
        assert(takahashi_count(a, b) == a);
        assert(1 <= a && a <= 12);
        assert(0 <= takahashi_count(a, b) && takahashi_count(a, b) <= 12);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures 
        result as int == takahashi_count(a as int, b as int) &&
        (a > b ==> result as int == a as int - 1) &&
        (a <= b ==> result as int == a as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): compute using i8 and prove relation to spec */
{
    let result: i8 = if a > b { a - 1 } else { a };
    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        reveal(takahashi_count);
        if ai > bi {
            assert(result as int == ai - 1);
            assert(takahashi_count(ai, bi) == ai - 1);
        } else {
            assert(result as int == ai);
            assert(takahashi_count(ai, bi) == ai);
        }
        assert(result as int == takahashi_count(ai, bi));
        lemma_count_bounds(ai, bi);
    }
    result
}

// </vc-code>


}

fn main() {}