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
/* code modified by LLM (iteration 3): remove ghost type usage by performing arithmetic with i8 */
{
    let mut total: i8 = 0;
    let mut remainder: i8 = n;

    total += remainder / 100;
    remainder = remainder % 100;

    total += remainder / 20;
    remainder = remainder % 20;

    total += remainder / 10;
    remainder = remainder % 10;

    total += remainder / 5;
    remainder = remainder % 5;

    total += remainder;

    total
}
// </vc-code>

}

fn main() {}