// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)

    ensures
        res.is_some() ==> res.unwrap() == x + y,
// </vc-spec>
// <vc-code>
{
    if x >= 0 && y >= 0 && x <= i32::MAX - y {
        Some(x + y)
    } else if x < 0 && y < 0 && x >= i32::MIN - y {
        Some(x + y)
    } else if (x >= 0 && y < 0) || (x < 0 && y >= 0) {
        Some(x + y)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}