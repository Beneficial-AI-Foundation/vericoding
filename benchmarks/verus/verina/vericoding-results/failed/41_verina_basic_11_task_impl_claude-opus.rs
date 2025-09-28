// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Return u32 directly, let Verus handle nat conversion implicitly */
    let digit = (n as u32) % 10;
    digit
}
// </vc-code>

}
fn main() {}