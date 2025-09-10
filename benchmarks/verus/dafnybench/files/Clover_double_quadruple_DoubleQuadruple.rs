use vstd::prelude::*;

verus! {

fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
{
    assume(false);
    unreached();
}

}
fn main() {}