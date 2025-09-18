// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches by casting literals to `nat` and `num` to `nat` when performing arithmetic operations. This addresses compilation errors where `nat` was expected but an integer was found. */
    if n == 0 { false } else {
        let mut num: nat = n;
        while num > (1 as nat)
            invariant
                num > (0 as nat),
            decreases num
        {
            if num % (4 as nat) != (0 as nat) {
                return false;
            }
            num = num / (4 as nat);
        }
        num == (1 as nat)
    }
}
// </vc-code>

}
fn main() {}