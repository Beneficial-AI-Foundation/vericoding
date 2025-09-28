// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn last_digit_helper(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
{
    n % 10
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
    /* code modified by LLM (iteration 5): ensure proof block returns () */
    proof {
        let result = last_digit_helper(n);
        assert(result < 10);
        assert(result == n % 10);
    }
    (n % 10) as int
}
// </vc-code>

}
fn main() {}