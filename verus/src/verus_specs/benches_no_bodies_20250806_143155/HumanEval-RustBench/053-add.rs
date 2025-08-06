use vstd::prelude::*;

verus! {

fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
{
    return None;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
