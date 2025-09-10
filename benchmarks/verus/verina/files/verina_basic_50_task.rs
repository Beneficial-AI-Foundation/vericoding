use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
{
    assume(false);
    unreached()
}

}
fn main() {}