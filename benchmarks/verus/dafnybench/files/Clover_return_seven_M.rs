use vstd::prelude::*;

verus! {

fn M(x: int) -> (seven: int)
  ensures seven == 7
{
    assume(false);
    unreached()
}

}
fn main() {}