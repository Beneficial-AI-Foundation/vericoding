use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this simple calculation.
// </vc-helpers>

// <vc-spec>
fn median_length(a: int, b: int) -> (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    // The problem statement guarantees a and b are greater than 0.
    // We need to prove that (a + b) / 2 is the median length.
    // Since this is a simple arithmetic calculation and Verus can handle integer division
    // automatically, no complex helper functions or proofs are needed for the `median_length` itself.

    // Calculate the median directly as specified in the ensures clause.
    let median_val: int = (a + b) / 2;

    // The postcondition `median == (a + b) / 2` is directly satisfied by the assignment.
    // Verus's SMT solver can usually prove simple arithmetic identities like this.
    
    median_val
}
// </vc-code>

fn main() {}

}