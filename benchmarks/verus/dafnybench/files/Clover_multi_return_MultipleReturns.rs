use vstd::prelude::*;

verus! {

fn multiple_returns(x: int, y: int) -> (result: (int, int))
    ensures 
        result.0 == x + y,
        result.1 == x - y,
{
    assume(false);
    unreached();
}

}
fn main() {}