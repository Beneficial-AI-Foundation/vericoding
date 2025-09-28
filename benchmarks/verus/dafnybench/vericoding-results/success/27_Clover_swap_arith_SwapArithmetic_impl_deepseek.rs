use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn swap_arithmetic_lemma(x: i32, y: i32) 
    ensures 
        (y, x).0 == y && (y, x).1 == x,
{
}
// </vc-helpers>

// <vc-spec>
fn swap_arithmetic(x: i32, y: i32) -> (res: (i32, i32))
    ensures 
        res.0 == y && res.1 == x,
// </vc-spec>
// <vc-code>
{
    proof {
        swap_arithmetic_lemma(x, y);
    }
    (y, x)
}
// </vc-code>

fn main() {
}

} // verus!