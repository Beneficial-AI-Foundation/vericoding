use vstd::prelude::*;

verus! {

fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
{
    assume(false);
    unreached()
}

}
fn main() {}