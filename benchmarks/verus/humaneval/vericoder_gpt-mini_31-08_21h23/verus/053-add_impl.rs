use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    x.checked_add(y)
}
// </vc-code>

fn main() {}
}