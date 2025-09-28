// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn alternating_sum(n: int) -> int
    recommends n > 0
    decreases n
{
    if n <= 0 { 0 }
    else if n == 1 { -1 }
    else { alternating_sum(n - 1) + (if n % 2 == 0 { n } else { -n }) }
}

spec fn valid_input(n: int) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type annotations for integer literals */
proof fn lemma_alternating_sum_even(n: int)
    requires
        n > 0,
        n % 2 == 0
    ensures
        alternating_sum(n) == n / 2
    decreases n
{
    if n == 2 {
        assert(alternating_sum(2) == alternating_sum(1) + 2);
        assert(alternating_sum(1) == -1);
        assert(alternating_sum(2) == -1 + 2 == 1);
        assert(2int / 2int == 1int);
    } else {
        assert(n > 2);
        lemma_alternating_sum_odd(n - 1);
        assert(alternating_sum(n - 1) == (n - 1) / 2 - (n - 1));
        assert(alternating_sum(n) == alternating_sum(n - 1) + n);
        assert(alternating_sum(n) == (n - 1) / 2 - (n - 1) + n);
        assert(alternating_sum(n) == (n - 1) / 2 + 1);
        assert((n - 1) / 2 + 1 == n / 2);
    }
}

proof fn lemma_alternating_sum_odd(n: int)
    requires
        n > 0,
        n % 2 != 0
    ensures
        alternating_sum(n) == n / 2 - n
    decreases n
{
    if n == 1 {
        assert(alternating_sum(1) == -1);
        assert(1int / 2int == 0int);
        assert(1int / 2int - 1int == -1int);
    } else {
        assert(n > 1);
        lemma_alternating_sum_even(n - 1);
        assert(alternating_sum(n - 1) == (n - 1) / 2);
        assert(alternating_sum(n) == alternating_sum(n - 1) - n);
        assert(alternating_sum(n) == (n - 1) / 2 - n);
        assert((n - 1) / 2 == n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == alternating_sum(n as int) &&
        (n as int % 2 == 0 ==> result as int == n as int / 2) &&
        (n as int % 2 != 0 ==> result as int == n as int / 2 - n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): No changes needed to main code */
{
    if n % 2 == 0 {
        proof {
            lemma_alternating_sum_even(n as int);
        }
        (n / 2) as i8
    } else {
        proof {
            lemma_alternating_sum_odd(n as int);
        }
        (n / 2 - n) as i8
    }
}
// </vc-code>


}

fn main() {}