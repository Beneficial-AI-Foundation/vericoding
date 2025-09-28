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
    
    // Count 100s
    let hundreds = remaining / 100;
    count = count + hundreds;
    remaining = remaining - hundreds * 100;
    
    // Count 20s
    let twenties = remaining / 20;
    count = count + twenties;
    remaining = remaining - twenties * 20;
    
    // Count 10s
    let tens = remaining / 10;
    count = count + tens;
    remaining = remaining - tens * 10;
    
    // Count 5s
    let fives = remaining / 5;
    count = count + fives;
    remaining = remaining - fives * 5;
    
    // Count 1s
    count = count + remaining;
    
    count
}
// </vc-code>

}

fn main() {}