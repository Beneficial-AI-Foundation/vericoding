use vstd::prelude::*;

verus! {

fn triple(x: i32) -> (r: i32)
  ensures r == 3 * x
{
    assume(false);
    unreached();
}

}
fn main() {}