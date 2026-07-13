// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn profit(a: nat, d: nat) -> int {
    (a * d) as int + 1 - pow2(d) as int
}

spec fn pow2(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

fn solve_max_profit_days(a: u32) -> (result: (u32, u32))
    requires a >= 2,
    ensures 
        result.0 >= result.1,
        result.0 >= 0,
        result.1 >= 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}
// </vc-code>


}

fn main() {
    // let test_cases = vec![5, 8, 9, 1000000000];
    // for a in test_cases {
    //     let (d1, d2) = solve_max_profit_days(a);
    //     println!("{} {}", d1, d2);
    // }
}