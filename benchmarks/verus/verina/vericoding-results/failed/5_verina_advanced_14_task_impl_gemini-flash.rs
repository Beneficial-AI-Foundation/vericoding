// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type casting from `nat` to `u64` for bitwise operations by directly accepting `int` as input and adding a precondition. */
spec fn is_power_of_two_spec(n: int) -> bool
    requires n >= 0
{
    n > 0 && (n as u64).spec_bitand((n - 1) as u64) == 0
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Modified `is_power_of_two_spec` to accept `int` to avoid type casting issues, adjusted the `count` invariant, and ensured `pow` function arguments are of type `nat`. Changed `n.into()` to `n as int` for `is_power_of_two_spec` argument. */
{
    if n == 0 {
        return false;
    }

    if !is_power_of_two_spec(n as int) {
        return false;
    }

    let mut num: nat = n;
    let mut count: nat = 0;
    while num > 1
        invariant 
            num > 0,
            count >= 0,
            is_power_of_two_spec(n as int) ==> (n == num * pow(2, count)), 
        decreases num
    {
        num = (num / 2) as nat;
        count = (count + 1) as nat;
    }
    count % 2 == 0
}
// </vc-code>

}
fn main() {}