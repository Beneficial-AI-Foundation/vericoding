// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_nth_sequence_element(n: nat) -> (result: nat)
    requires n > 0,
    ensures result < n
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // #eval find_nth_sequence_element 8
    // #eval find_nth_sequence_element 9
    // #eval find_nth_sequence_element 20
}