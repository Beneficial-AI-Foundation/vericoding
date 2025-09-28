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
/* helper modified by LLM (iteration 2): prove bounds for takahashi_count within the valid input range */
proof fn takahashi_bounds(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        0 <= takahashi_count(a, b),
        takahashi_count(a, b) <= 12,
{
    if a > b {
        assert(takahashi_count(a, b) == a - 1);
        assert(1 <= a && a <= 12);
        assert(0 <= a - 1);
        assert(a - 1 <= 11);
        assert(0 <= takahashi_count(a, b));
        assert(takahashi_count(a, b) <= 11);
    } else {
        assert(takahashi_count(a, b) == a);
        assert(1 <= a && a <= 12);
        assert(0 <= a);
        assert(a <= 12);
        assert(0 <= takahashi_count(a, b));
        assert(takahashi_count(a, b) <= 12);
    }
}

/* helper modified by LLM (iteration 2): relate i8 and int orderings via casts */
proof fn i8_int_ordering_compat(a: i8, b: i8)
    ensures
        (a > b) == ((a as int) > (b as int)),
        (a <= b) == ((a as int) <= (b as int)),
{
    if a > b {
        assert((a as int) > (b as int));
        assert(!((a as int) <= (b as int)));
    } else {
        assert(a <= b);
        assert((a as int) <= (b as int));
        assert(!((a as int) > (b as int)));
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
{
    /* code modified by LLM (iteration 2): avoid non-ghost ints in exec; compute with i8 and prove spec equality */
    let result: i8;
    if a > b {
        proof {
            assert(1 <= a as int && a as int <= 12);
            assert(-128 <= (a as int) - 1 && (a as int) - 1 <= 127);
        }
        result = a - 1;
    } else {
        result = a;
    }

    proof {
        let ghost ai: int = a as int;
        let ghost bi: int = b as int;
        assert(valid_input(ai, bi));
        i8_int_ordering_compat(a, b);
        if a > b {
            assert(ai > bi);
            assert(takahashi_count(ai, bi) == ai - 1);
            assert(result as int == (a - 1) as int);
            assert((a - 1) as int == ai - 1);
        } else {
            assert(!(ai > bi));
            assert(ai <= bi);
            assert(takahashi_count(ai, bi) == ai);
            assert(result as int == a as int);
        }
    }

    result
}
// </vc-code>


}

fn main() {}