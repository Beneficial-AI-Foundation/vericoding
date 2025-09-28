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
/* code modified by LLM (iteration 4): [fix type usage for 'int' values in exec code] */
{
    let n_val = n as u16;

    let num_100: u16 = n_val / 100;
    let remaining_after_100: u16 = n_val % 100;

    let num_20: u16 = remaining_after_100 / 20;
    let remaining_after_20: u16 = remaining_after_100 % 20;

    let num_10: u16 = remaining_after_20 / 10;
    let remaining_after_10: u16 = remaining_after_20 % 10;

    let num_5: u16 = remaining_after_10 / 5;
    let remaining_after_5: u16 = remaining_after_10 % 5;

    let total_bills: u16 = num_100 + num_20 + num_10 + num_5 + remaining_after_5;

    total_bills as i8
}
// </vc-code>

}

fn main() {}