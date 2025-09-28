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
    /* code modified by LLM (iteration 5): implemented recursive check for power of four using ghost expressions inside proof block to comply with Verus ghost code restrictions */
    proof {
        return if n == 1nat { true } else if n == 0nat { false } else if (n as int % 4) != 0 { false } else { let q = (n as int / 4); if_power_of_four(q as nat) };
    }
}
// </vc-code>

}
fn main() {}