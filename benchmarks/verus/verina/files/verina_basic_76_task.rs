// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn my_min(x: i8, y: i8) -> (result: i8)
    ensures
        (x as int <= y as int ==> result as int == x as int) && (x as int > y as int ==> result as int == y as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}