// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn gcd(a: int, b: int) -> int
    decreases b when b >= 0
{
    if a > 0 && b >= 0 {
        if b == 0 { a } else { gcd(b, a % b) }
    } else {
        1  /* default for invalid input */
    }
}

spec fn lcm(a: int, b: int) -> int {
    if a > 0 && b > 0 {
        (a * b) / gcd(a, b)
    } else {
        1  /* default for invalid input */
    }
}

spec fn lcm_seq(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() > 0 {
        if nums.len() == 1 { 
            nums[0] 
        } else { 
            lcm(nums[0], lcm_seq(nums.skip(1)))
        }
    } else {
        1  /* default for empty sequence */
    }
}

spec fn valid_input(periods: Seq<int>) -> bool {
    periods.len() > 0 && periods.len() <= 100 &&
    forall|i: int| 0 <= i < periods.len() ==> periods[i] > 0
}

spec fn correct_result(periods: Seq<int>, result: int) -> bool {
    valid_input(periods) ==> result == lcm_seq(periods)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_minimum_time(periods: Vec<i8>) -> (result: i8)
    requires valid_input(periods@.map(|i: int, v: i8| v as int))
    ensures correct_result(periods@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}