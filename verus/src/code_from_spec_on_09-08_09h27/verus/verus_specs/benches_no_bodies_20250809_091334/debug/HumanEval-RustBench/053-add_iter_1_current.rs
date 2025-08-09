use vstd::prelude::*;

verus! {

fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
{
    if x > 0 && y > 0 && x > i32::MAX - y {
        None
    } else if x < 0 && y < 0 && x < i32::MIN - y {
        None
    } else {
        Some(x + y)
    }
}

}
fn main() {}