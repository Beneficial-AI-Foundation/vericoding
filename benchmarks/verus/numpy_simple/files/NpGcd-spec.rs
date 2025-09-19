// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn gcd_int(a: i8, b: i8) -> (result: i8)
    ensures
        result >= 0,
        (a as int) % (result as int) == 0,
        (b as int) % (result as int) == 0,
        forall|d: int| d > 0 && #[trigger] ((a as int) % d) == 0 && #[trigger] ((b as int) % d) == 0 ==> d <= (result as int),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}