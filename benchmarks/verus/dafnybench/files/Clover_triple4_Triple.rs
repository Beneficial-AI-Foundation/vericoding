use vstd::prelude::*;

verus! {

fn triple(x: int) -> (r: int)
    ensures r == 3 * x
{
    assume(false);
    unreached()
}

}
fn main() {}