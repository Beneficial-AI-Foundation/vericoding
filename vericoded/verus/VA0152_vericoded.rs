// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn is_minimal_steps(x: int, steps: int) -> bool {
    x >= 1 ==> (steps >= 1 &&
    steps * 5 >= x &&
    (steps - 1) * 5 < x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma establishing minimality of ceil(x/5) for x >= 1 */
proof fn lemma_ceil5_minimal(x: int)
    ensures
        is_minimal_steps(x, ((x + 4) / 5)),
{
    if x >= 1 {
        let s = (x + 4) / 5;
        let r = (x + 4) % 5;
        assert(0 <= r && r < 5);
        assert(x + 4 == 5*s + r);

        // s*5 >= x
        assert(x == 5*s + r - 4);
        assert(r - 4 <= 0);
        assert(x <= 5*s);

        // (s - 1)*5 < x
        assert(5*s - 5 < 5*s - 4);
        assert(5*s - 4 <= 5*s + r - 4);
        assert((s - 1)*5 < x);

        // s >= 1
        if s == 0 {
            assert(x + 4 == r);
            assert(x + 4 < 5);
            assert(x < 1);
            assert(false);
        }
    }
}

/* helper modified by LLM (iteration 2): lemma showing ceil(x/5) <= x for x >= 1 */
proof fn lemma_ceil5_le_x(x: int)
    ensures
        x >= 1 ==> ((x + 4) / 5) <= x,
{
    if x >= 1 {
        let s = (x + 4) / 5;
        let r = (x + 4) % 5;
        assert(0 <= r && r < 5);
        assert(x + 4 == 5*s + r);
        assert(5*s <= x + 4);
        if s <= x {
        } else {
            assert(s >= x + 1);
            assert(5*s >= 5*x + 5);
            assert(5*x + 5 > x + 4);
            assert(5*s > x + 4);
            assert(5*s <= x + 4);
            assert(false);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn min_steps(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_steps(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute steps via a loop adding 5 until reaching x; maintain invariants and prove minimality without using exec 'int' vars */
    let mut steps: i16 = 0;
    let mut total: i16 = 0;

    proof {
        let xi: int = x as int;
        assert(xi >= 1);
        assert((xi + 4) >= 5);
        assert(((xi + 4) / 5) >= 1);
    }

    while total < x as i16
        invariant
            (steps as int) >= 0,
            (steps as int) <= ((x as int + 4) / 5),
            (total as int) == 5 * (steps as int),
        decreases ((x as int + 4) / 5) - (steps as int)
    {
        proof {
            let xi: int = x as int;
            let s: int = (xi + 4) / 5;
            lemma_ceil5_minimal(xi);
            assert((total as int) < xi);
            assert((total as int) == 5 * (steps as int));
            if !((steps as int) < s) {
                assert((steps as int) >= s);
                assert(5 * (steps as int) >= 5 * s);
                assert(5 * s >= xi);
                assert((total as int) >= xi);
                assert(false);
            }
            assert(((steps as int) + 1) <= s);
        }
        total = total + 5;
        steps = steps + 1;
    }

    proof {
        let xi: int = x as int;
        let s: int = (xi + 4) / 5;
        lemma_ceil5_minimal(xi);
        assert((total as int) >= xi);
        assert((total as int) == 5 * (steps as int));
        assert((steps as int) <= s);
        if (steps as int) < s {
            assert(5 * (steps as int) <= 5 * (s - 1));
            assert(5 * (s - 1) < xi);
            assert(5 * (steps as int) < xi);
            assert(false);
        }
        assert((steps as int) >= s);
        assert((steps as int) == s);
    }

    proof {
        let xi: int = x as int;
        let s: int = (xi + 4) / 5;
        lemma_ceil5_le_x(xi);
        assert((steps as int) == s);
        assert(s <= xi);
        assert(xi <= 127);
        assert((steps as int) <= 127);
        assert((steps as int) >= 1);
    }

    let result: i8 = steps as i8;

    proof {
        assert((result as int) == (steps as int));
        let xi: int = x as int;
        let s: int = (xi + 4) / 5;
        lemma_ceil5_minimal(xi);
        assert((steps as int) == s);
        assert(is_minimal_steps(xi, (steps as int)));
    }

    result
}
// </vc-code>


}

fn main() {}