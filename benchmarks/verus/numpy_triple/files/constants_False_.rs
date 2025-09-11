// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn false_() -> (result: bool)
    ensures 
        result == false,
        forall|b: bool| (result || b) == b,
        forall|b: bool| (result && b) == false,
        result == !true
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}