use vstd::prelude::*;

verus! {

fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
{
    if x.checked_add(y).is_some() {
        Some(x + y)
    } else {
        None
    }
}

}
fn main() {}