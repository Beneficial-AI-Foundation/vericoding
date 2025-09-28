// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3
}

spec fn min_jumps(n: int) -> int
    recommends valid_input(n)
{
    (n - 2) * (n - 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute min_jumps for i8 input as int */
spec fn min_jumps_i8(n: i8) -> int {
    (n as int - 2) * (n as int - 2)
}

/* helper modified by LLM (iteration 5): lemma equating i8-based spec to int spec */
proof fn lemma_min_jumps_i8_equiv(n: i8)
    requires valid_input(n as int)
    ensures min_jumps_i8(n) == min_jumps(n as int)
{
    proof {
        // both sides expand to (n as int - 2) * (n as int - 2)
        assert(min_jumps_i8(n) == (n as int - 2) * (n as int - 2));
        assert(min_jumps(n as int) == (n as int - 2) * (n as int - 2));
        assert(min_jumps_i8(n) == min_jumps(n as int));
    }
}

/* helper modified by LLM (iteration 5): lemma relating i8 square (t*t) cast to int to the spec */
proof fn lemma_i8_square_to_spec(n: i8)
    requires valid_input(n as int)
    ensures ((n - 2) * (n - 2)) as int == min_jumps(n as int)
{
    proof {
        lemma_min_jumps_i8_equiv(n);
        // (n - 2) as int == n as int - 2
        assert(((n - 2) as int) == n as int - 2);
        // cast of product equals product of casts
        assert(((n - 2) * (n - 2)) as int == ((n - 2) as int) * ((n - 2) as int));
        // combine to reach the specification
        assert(((n - 2) as int) * ((n - 2) as int) == min_jumps(n as int));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == min_jumps(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute square using i8 arithmetic to avoid int->i8 cast */
    let t: i8 = n - 2;
    let result: i8 = t * t;
    proof {
        lemma_i8_square_to_spec(n);
        assert((result as int) == min_jumps(n as int));
    }
    result
}

// </vc-code>


}

fn main() {}