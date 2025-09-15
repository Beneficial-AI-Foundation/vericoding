// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn calculate_deposit(initial: int, years: int) -> int
    recommends initial >= 0, years >= 0
    decreases years
{
    if years == 0 {
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
fn solve(x: int) -> (years: int)
    requires x >= 101
    ensures 
        years >= 0 &&
        calculate_deposit(100, years) >= x &&
        (years == 0 || calculate_deposit(100, years - 1) < x)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}