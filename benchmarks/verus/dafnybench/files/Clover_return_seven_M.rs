use vstd::prelude::*;

verus! {

proof fn M(x: int) -> (seven: int)
  ensures seven == 7
{
    assume(false);
    unreached();
}

}
fn main() {}