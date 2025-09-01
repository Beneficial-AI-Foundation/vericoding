use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    if x >= 0 && y >= 0 && x > i32::MAX - y {
        // Overflow case for positive numbers
        None
    } else if x < 0 && y < 0 && x < i32::MIN - y {
        // Overflow case for negative numbers
        None
    } else {
        // No overflow, safe to add
        Some(x + y)
    }
    // impl-end
}
// </vc-code>

fn main() {}
}