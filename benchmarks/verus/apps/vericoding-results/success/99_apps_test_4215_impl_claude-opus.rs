// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn uncovered_length(a: int, b: int) -> int {
    if a - 2 * b > 0 { a - 2 * b } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove arithmetic bounds and non-overflow */
proof fn lemma_solve_bounds(a: i8, b: i8)
    requires
        valid_input(a as int, b as int)
    ensures
        2 * (b as int) <= 200,
        (a as int) - 2 * (b as int) >= -199,
        (a as int) - 2 * (b as int) <= 100,
        if (a as int) > 2 * (b as int) { (a as int) - 2 * (b as int) >= 0 } else { true },
        b <= 63 ==> 2 * b <= 126,
        b > 63 ==> (a as int) <= 2 * (b as int)
{
    assert(b >= 1 && b <= 100);
    assert(a >= 1 && a <= 100);
    assert(2 * (b as int) >= 2 && 2 * (b as int) <= 200);
    if b > 63 {
        assert(2 * (b as int) > 126);
        assert((a as int) <= 100);
        assert((a as int) < 2 * (b as int));
    }
    if (a as int) > 2 * (b as int) {
        assert((a as int) - 2 * (b as int) > 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result >= 0,
        result as int == uncovered_length(a as int, b as int),
        result as int == if a as int > 2 * (b as int) { a as int - 2 * (b as int) } else { 0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int usage in executable code by using i8 comparisons */
    proof {
        lemma_solve_bounds(a, b);
    }
    
    if b <= 63 {
        // Safe to compute 2*b without overflow
        let two_b: i8 = 2 * b;
        proof {
            assert(two_b as int == 2 * (b as int));
        }
        if a > two_b {
            proof {
                assert((a as int) > 2 * (b as int));
                assert((a as int) - 2 * (b as int) > 0);
                assert((a as int) - 2 * (b as int) <= 100);
            }
            a - two_b
        } else {
            proof {
                assert((a as int) <= 2 * (b as int));
            }
            0
        }
    } else {
        // b > 63, so 2*b > 126, and since a <= 100, we know a < 2*b
        proof {
            assert(b > 63);
            assert(2 * (b as int) > 126);
            assert((a as int) <= 100);
            assert((a as int) < 2 * (b as int));
        }
        0
    }
}
// </vc-code>


}

fn main() {}