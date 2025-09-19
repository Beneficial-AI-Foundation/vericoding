// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn last_digit(n: nat) -> nat
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    n % 10
    // impl-end
}

proof fn last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10,
        last_digit(n) == n % 10,
{
    // impl-start
    assume(false); // TODO: Remove this line and implement the proof
    // impl-end
}
// </vc-code>


}
fn main() {}