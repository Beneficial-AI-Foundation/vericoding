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
{
    let mut remaining = n;
    let mut count: i8 = 0;

    count = count + remaining / 100;
    remaining = remaining % 100;

    count = count + remaining / 20;
    remaining = remaining % 20;

    count = count + remaining / 10;
    remaining = remaining % 10;

    count = count + remaining / 5;
    remaining = remaining % 5;

    count = count + remaining;

    count
}
// </vc-code>

}

fn main() {}