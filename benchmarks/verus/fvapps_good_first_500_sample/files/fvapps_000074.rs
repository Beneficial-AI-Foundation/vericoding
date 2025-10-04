// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_square_side(n: nat) -> (result: nat)
    requires n >= 3,
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


proof fn min_square_side_positive(n: nat)
    requires n >= 3
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn min_square_side_monotone(n: nat)
    requires n >= 3
{
    assume(false); // TODO: Remove this line and implement the proof
}

}
fn main() {}