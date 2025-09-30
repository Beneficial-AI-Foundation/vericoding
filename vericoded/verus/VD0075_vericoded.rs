use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: int, y: int) -> (result: (int, int))
    ensures 
        result.0 == x + y,
        result.1 == x - y,
// </vc-spec>
// <vc-code>
{
    (x + y, x - y)
}
// </vc-code>

fn main() {
}

}