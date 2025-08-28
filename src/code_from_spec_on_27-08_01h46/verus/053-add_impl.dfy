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
    match x.checked_add(y) {
        Some(sum) => Some(sum),
        None => None,
    }
    // impl-end
}
// </vc-code>

}
fn main() {}