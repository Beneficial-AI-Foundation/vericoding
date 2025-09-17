// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn gcd_int(a: i32, b: i32) -> (result: i32)
    ensures
        result >= 0,
        a % result == 0,
        b % result == 0,
        forall|d: i32| d > 0 && #[trigger] (a % d) == 0 && #[trigger] (b % d) == 0 ==> d <= result,
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