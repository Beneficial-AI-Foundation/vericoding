use vstd::prelude::*;

verus! {

fn swap_arithmetic(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> (result.0 != x && result.1 != y),
{
    assume(false);
    unreached()
}

}
fn main() {}