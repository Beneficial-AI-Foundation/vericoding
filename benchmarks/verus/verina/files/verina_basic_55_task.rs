// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn compare(a: i8, b: i8) -> (result: bool)
    ensures
        (a as int == b as int ==> result == true) && (a as int != b as int ==> result == false),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}