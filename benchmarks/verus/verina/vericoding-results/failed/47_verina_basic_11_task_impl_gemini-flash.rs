// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This section is intentionally left blank as no helpers are needed for this problem. */
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Direct calculation of modulo with nat types. */
{
    n % 10
}
// </vc-code>

}
fn main() {}