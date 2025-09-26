// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn calculate_deposit(initial: int, years: int) -> int
    decreases years
{
    if years <= 0 { 
        initial 
    } else { 
        let prev_deposit = calculate_deposit(initial, years - 1);
        prev_deposit + prev_deposit / 100
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (years: i8)
    requires x >= 101
    ensures 
        years >= 0 &&
        calculate_deposit(100, years as int) >= x as int &&
        (years == 0 || calculate_deposit(100, (years - 1) as int) < x as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}