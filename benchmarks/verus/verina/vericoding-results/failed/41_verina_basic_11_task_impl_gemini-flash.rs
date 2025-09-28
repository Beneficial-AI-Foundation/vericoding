// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `last_digit` helper is no longer needed since the `last_digit` function is a spec function.*/

// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The type error `expected `nat`, found integer` is resolved by casting the result of `n % 10` to `nat`. */
{
    (n % 10) as nat
}
// </vc-code>

}
fn main() {}