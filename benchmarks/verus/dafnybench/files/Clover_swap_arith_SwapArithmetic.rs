use vstd::prelude::*;

verus! {

fn swap_arithmetic(x: i32, y: i32) -> (res: (i32, i32))
    ensures 
        res.0 == y && res.1 == x,
{
    assume(false);
    unreached()
}

}
fn main() {}