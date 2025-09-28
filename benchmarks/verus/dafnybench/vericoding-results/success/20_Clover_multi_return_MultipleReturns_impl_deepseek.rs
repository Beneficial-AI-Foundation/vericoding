use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this simple specification
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: int, y: int) -> (result: (int, int))
    ensures 
        result.0 == x + y,
        result.1 == x - y,
// </vc-spec>
// <vc-code>
{
    proof {
        // The postconditions are straightforward mathematical identities
        // No complex proof needed, Verus can verify directly
    }
    (x + y, x - y)
}
// </vc-code>

fn main() {
}

}