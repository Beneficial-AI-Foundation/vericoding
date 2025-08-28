use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn add(x: i32, y: i32) -> (res: Option<i32>)
    ensures
        res.is_some() ==> res.unwrap() == x + y,
{
    Some(x + y)
}
// </vc-code>

}
fn main() {}