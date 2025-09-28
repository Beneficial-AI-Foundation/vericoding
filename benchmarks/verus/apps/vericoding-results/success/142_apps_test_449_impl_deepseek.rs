// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        n >= 1
    }
    
    spec fn min_bills(n: int) -> int
        recommends n >= 1
    {
        n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
    }
// </vc-preamble>

// <vc-helpers>
proof fn lemma_min_bills_nonnegative(n: int)
    requires n >= 1
    ensures min_bills(n) >= 0
{
    /* helper modified by LLM (iteration 4): Simplified and more efficient proof */
    assert(min_bills(n) >= 0) by {
        assert(min_bills(n) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result >= 0,
        result as int == min_bills(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Optimized to avoid resource limit */
    let div100 = n / 100;
    let rem100 = n % 100;
    let div20 = rem100 / 20;
    let rem20 = rem100 % 20;
    let div10 = rem20 / 10;
    let rem10 = rem20 % 10;
    let div5 = rem10 / 5;
    let rem5 = rem10 % 5;
    
    (div100 + div20 + div10 + div5 + rem5) as i8
}
// </vc-code>

}

fn main() {}