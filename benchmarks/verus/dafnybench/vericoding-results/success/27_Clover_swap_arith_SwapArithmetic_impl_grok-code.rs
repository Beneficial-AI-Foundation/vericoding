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
    let sum: i64 = (x as i64) + (y as i64);
    let res1: i64 = sum - (x as i64);
    let res0: i64 = sum - (y as i64);
    assert(res1 == y as i64);
    assert(res0 == x as i64);
    (res1 as i32, res0 as i32)
}
// </vc-code>

fn main() {
}

} // verus!