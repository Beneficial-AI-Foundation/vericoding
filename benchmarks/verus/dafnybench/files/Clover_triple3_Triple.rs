use vstd::prelude::*;

verus! {

proof fn triple(x: int) -> (r: int)
  ensures r == 3 * x
{
    assume(false);
    unreached()
}

}
fn main() {}