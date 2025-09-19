// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn allow_42(x: i8, y: i8) -> (ret: (i8, bool))
    ensures 
        (y as int != 42 ==> ret.0 as int == (x as int / (42int - y as int)) && ret.1 == false) &&
        (y as int == 42 ==> ret.0 as int == 0 && ret.1 == true)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}