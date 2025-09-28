use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: int, b: int) -> (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
    // The proof for simple multiplication can often be handled directly by Verus's SMT solver
    // without explicit `proof { ... }` blocks for basic arithmetic operations.
    // However, if the Verus SMT solver struggles with proving the `ensures` clause directly
    // for `a * b`, an explicit assert could be added for clarity or to guide the solver,
    // though for integers, it's usually not necessary.

    // assert(a * b == a * b); // Trivial, but demonstrates an assert if needed

    // The result is simply the product of a and b.
    // Verus will try to prove that `a * b` (the return value) equals `a * b` (from the ensures clause).
    a * b
}
// </vc-code>

fn main() {}

}