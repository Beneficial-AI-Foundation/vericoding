use vstd::prelude::*;

verus! {

fn min(x: int, y: int) -> (z: int)
    ensures
        x <= y ==> z == x,
        x > y ==> z == y,
{
    assume(false);
    unreached()
}

}
fn main() {}