// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches by converting integers to nat in comparisons and operations */
fn is_power_of_four_recursive(n: nat) -> bool
    decreases n
{
    if n == (0 as nat) {
        false
    } else if n == (1 as nat) {
        true
    } else {
        if n % (4 as nat) == (0 as nat) {
            is_power_of_four_recursive(n / (4 as nat))
        } else {
            false
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using fixed helper with correct type conversions */
{
    is_power_of_four_recursive(n)
}
// </vc-code>

}
fn main() {}