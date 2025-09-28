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
proof fn alternating_sum_spec_even(n: int) 
    requires n > 0 && n % 2 == 0,
    ensures alternating_sum(n) == n / 2 
    decreases n 
{ 
    if n == 2 {
        assert(alternating_sum(2) == 1) by (compute);
    } else if n >= 4 {
        alternating_sum_spec_even(n - 2);
        assert(alternating_sum(n) == alternating_sum(n - 2) + n - (n - 1)) by {
            assert(alternating_sum(n) == alternating_sum(n - 1) + n);
            assert(alternating_sum(n - 1) == alternating_sum(n - 2) + (-(n - 1)));
        };
        assert(n / 2 == (n - 2) / 2 + 1);
    }
}

proof fn alternating_sum_spec_odd(n: int) 
    requires n > 0 && n % 2 != 0, 
    ensures alternating_sum(n) == n / 2 - n 
    decreases n 
{ 
    if n == 1 {
        assert(alternating_sum(1) == -1);
        assert(1int / 2 - 1 == -1);
    } else if n >= 3 {
        alternating_sum_spec_odd(n - 2);
        assert(alternating_sum(n) == alternating_sum(n - 1) + (-n)) by {
            assert(alternating_sum(n) == alternating_sum(n - 1) + (if n % 2 == 0 { n } else { -n }));
        };
        assert(alternating_sum(n - 1) == alternating_sum(n - 2) + (n - 1)) by {
            assert((n - 1) % 2 == 0);
        };
        assert(alternating_sum(n) == alternating_sum(n - 2) + (n - 1) - n);
        assert(n / 2 - n == (n - 2) / 2 - (n - 2) + (n - 1) - n);
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
{
    /* code modified by LLM (iteration 3): fixed integer literal type annotation */
    proof {
        if n as int % 2 == 0 {
            alternating_sum_spec_even(n as int);
        } else {
            alternating_sum_spec_odd(n as int);
        }
    }
    let half = n / 2;
    if n % 2 == 0 {
        half
    } else {
        half - n
    }
}
// </vc-code>


}

fn main() {}