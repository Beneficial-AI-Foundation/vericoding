use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    // impl-start
    let sum = x.checked_add(y);
    if sum.is_some() {
        assert(sum.unwrap() == x + y); // This assertion is automatically proven due to checked_add's semantics
        Some(sum.unwrap())
    } else {
        None
    }
    // impl-end
}
// </vc-code>

fn main() {}
}