// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute remainder by repeated subtraction, ensure < 10 */
fn mod_remainder_lt(n: nat) -> (result: nat)
    ensures
        result < 10,
{
    let mut r: nat = n;
    while r >= 10
        invariant
            r <= n,
        decreases
            r,
    {
        r = r - 10;
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute last digit using repeated-subtraction helper */
    let result = mod_remainder_lt(n);
    result
}
// </vc-code>

}
fn main() {}