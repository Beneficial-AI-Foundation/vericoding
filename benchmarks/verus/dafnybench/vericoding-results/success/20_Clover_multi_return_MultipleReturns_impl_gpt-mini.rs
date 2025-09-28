use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: int, y: int) -> (result: (int, int))
    ensures 
        result.0 == x + y,
        result.1 == x - y,
// </vc-spec>
// <vc-code>
{
    let a = x + y;
    let b = x - y;
    (a, b)
}
// </vc-code>

fn main() {
}

}