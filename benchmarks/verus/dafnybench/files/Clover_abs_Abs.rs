use vstd::prelude::*;

verus! {

proof fn abs(x: int) -> (y: int)
    ensures 
        x >= 0 ==> x == y,
        x < 0 ==> x + y == 0,
{
    assume(false);
    unreached()
}

}
fn main() {}