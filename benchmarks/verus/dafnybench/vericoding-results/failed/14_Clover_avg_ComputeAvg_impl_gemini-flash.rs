use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    // The Verus `int` type supports standard integer division which truncates toward zero.
    // The specification requires an average that is equivalent to `(a + b) / 2`.
    // For integers, in Verus, (a + b) / 2 correctly implements this for all integer values.
    // No special handling for positive/negative numbers is needed as Verus's default
    // integer division behaves as expected for this simple case.

    // Calculate the sum of a and b.
    let sum = a + b;

    // Calculate the average by dividing the sum by 2.
    // Verus's integer division `sum / 2` will perform the required truncation
    // consistent with the `(a + b) / 2` specification.
    let avg = sum / 2;

    avg
}
// </vc-code>

fn main() {
}

}