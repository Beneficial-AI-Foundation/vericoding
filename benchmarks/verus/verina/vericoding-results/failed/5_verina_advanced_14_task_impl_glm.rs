// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type issues by using nat consistently and casting pow result to nat */
fn check_power_of_four(n: nat) -> (result: bool)
    ensures result == (exists|m: nat| n == pow(4, m))
{
    let mut m: nat = 0;
    let mut current: nat = 1;
    
    while current <= n
        invariant (current == pow(4, m) as nat && m <= n)
    {
        if current == n {
            return true;
        }
        m = m + 1;
        current = pow(4, m) as nat;
    }
    
    false
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): maintained helper call with fixed helper types */
{
    check_power_of_four(n)
}
// </vc-code>

}
fn main() {}