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
    /* code modified by LLM (iteration 5): use int arithmetic and convert with spec mode verification */
    let result_int = n as int % 10;
    let result = result_int as nat;
    result
}
// </vc-code>

}
fn main() {}