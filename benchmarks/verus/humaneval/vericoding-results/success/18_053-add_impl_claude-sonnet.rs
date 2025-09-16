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
    if x > 0 && y > i32::MAX - x {
        None
    } else if x < 0 && y < i32::MIN - x {
        None
    } else {
        Some(x + y)
    }
}
// </vc-code>

}
fn main() {}