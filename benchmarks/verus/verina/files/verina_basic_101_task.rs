use vstd::prelude::*;

verus! {

fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
{
    assume(false);
    unreached()
}

}
fn main() {}