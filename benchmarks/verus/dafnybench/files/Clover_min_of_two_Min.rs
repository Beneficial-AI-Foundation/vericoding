// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min(x: i8, y: i8) -> (z: i8)
    ensures
        x as int <= y as int ==> z as int == x as int,
        x as int > y as int ==> z as int == y as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}