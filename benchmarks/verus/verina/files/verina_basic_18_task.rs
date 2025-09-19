// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sum_of_digits(n: nat) -> nat;
// </vc-spec>
// <vc-code>
proof fn sum_of_digits_spec_satisfied(n: nat)
    ensures sum_of_digits(n) >= 0,
{
    // impl-start
    assume(false); // TODO: Remove this line and implement the proof
    // impl-end
}
// </vc-code>


}
fn main() {}