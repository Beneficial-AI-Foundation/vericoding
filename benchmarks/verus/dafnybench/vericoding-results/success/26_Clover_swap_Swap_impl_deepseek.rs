use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swap(x: i32, y: i32) -> (result: (i32, i32))
    ensures 
        result.0 == y,
        result.1 == x,
// </vc-spec>
// <vc-code>
{
    (y, x)
}
// </vc-code>

fn main() {
}

}