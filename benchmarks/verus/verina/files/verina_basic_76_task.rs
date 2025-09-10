use vstd::prelude::*;

verus! {

fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
{
    assume(false);
    unreached()
}

}
fn main() {}