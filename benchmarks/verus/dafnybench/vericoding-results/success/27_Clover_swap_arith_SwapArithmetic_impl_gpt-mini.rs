use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swap_arithmetic(x: i32, y: i32) -> (res: (i32, i32))
    ensures 
        res.0 == y && res.1 == x,
// </vc-spec>
// <vc-code>
{
    (y, x)
}
// </vc-code>

fn main() {
}

} // verus!