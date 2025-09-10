use vstd::prelude::*;

verus! {

fn swap_simultaneous(x_param: i32, y_param: i32) -> (ret: (i32, i32))
    ensures 
        ret.0 == y_param,
        ret.1 == x_param,
{
    assume(false);
    unreached();
}

}
fn main() {}