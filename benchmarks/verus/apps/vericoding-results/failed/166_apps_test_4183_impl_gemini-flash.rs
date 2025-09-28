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
/* helper modified by LLM (iteration 5): Removed unused helper */
// </vc-helpers>

// <vc-spec>
fn find_minimum_time(periods: Vec<i8>) -> (result: i8)
    requires valid_input(periods@.map(|i: int, v: i8| v as int))
    ensures correct_result(periods@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    let ghost s_periods = periods@.map(|i: int, v: i8| v as int);

    let mut current_lcm: int = 1;
    if s_periods.len() > (0 as nat) {
        current_lcm = s_periods.index(0);
        let mut i: nat = 1;
        while i < s_periods.len()
            invariant
                0 <= i,
                i <= s_periods.len(),
                current_lcm > 0,
                forall|j: int| 0 <= j < i ==> s_periods.index(j) > 0,
                current_lcm == lcm_seq(s_periods.subsequence(0, i as int)),
            decreases (s_periods.len() - i as int)
        {
            let next_val: int = s_periods.index(i as int);
            current_lcm = lcm(current_lcm, next_val);
            i = (i + 1) as nat;
        }
    }

    (current_lcm as i8)
}
// </vc-code>


}

fn main() {}