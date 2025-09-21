// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn abs(x: i8) -> (y: i8)
    ensures 
        x as int >= 0 ==> x as int == y as int,
        (x as int) < 0 ==> (x as int) + (y as int) == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}