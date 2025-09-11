// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn allow_42(x: i32, y: i32) -> (ret: (i32, bool))
    ensures 
        (y != 42 ==> ret.0 == (x as int / (42int - y as int)) as i32 && ret.1 == false) &&
        (y == 42 ==> ret.0 == 0 && ret.1 == true)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}