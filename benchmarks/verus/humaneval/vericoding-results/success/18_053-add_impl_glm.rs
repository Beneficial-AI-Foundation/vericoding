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
    let result = x.checked_add(y);
    result
}
// </vc-code>

}
fn main() {}