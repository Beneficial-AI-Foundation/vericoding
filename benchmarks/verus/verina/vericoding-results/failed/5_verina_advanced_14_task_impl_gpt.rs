// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_power_of_four(n: nat) -> bool {
    exists|m: nat| n == pow(4, m)
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    exists|m: nat| n == pow(4, m)
}
// </vc-code>

}
fn main() {}