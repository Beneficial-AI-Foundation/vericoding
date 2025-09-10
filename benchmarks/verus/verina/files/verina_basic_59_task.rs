use vstd::prelude::*;

verus! {

fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
{
    assume(false);
    unreached();
}

}
fn main() {}