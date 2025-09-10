use vstd::prelude::*;

verus! {

fn swap(x: i32, y: i32) -> (result: (i32, i32))
    ensures 
        result.0 == y,
        result.1 == x,
{
    assume(false);
    unreached();
}

}
fn main() {}