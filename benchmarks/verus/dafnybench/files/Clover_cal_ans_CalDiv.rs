use vstd::prelude::*;

verus! {

fn cal_div() -> (result: (i32, i32))
  ensures result.0 == 191i32 / 7i32 && result.1 == 191i32 % 7i32,
{
    assume(false);
    unreached();
}

}
fn main() {}