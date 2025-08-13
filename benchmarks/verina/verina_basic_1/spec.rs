use vstd::prelude::*;

verus! {

// <vc-dependencies>
spec fn hasOppositeSign_precond(a: int, b: int) -> bool {
    true
}
spec fn hasOppositeSign_postcond(a: int, b: int, result: bool) -> bool
recommends hasOppositeSign_precond(a, b)
{
    (((a < 0 && b > 0) || (a > 0 && b < 0)) ==> result) &&
    (!((a < 0 && b > 0) || (a > 0 && b < 0)) ==> !result)
}
// </vc-dependencies>

// <vc-helpers>

// </vc-helpers>

// <vc-task>
fn hasOppositeSign(a: int, b: int) -> (result: bool)
    requires hasOppositeSign_precond(a, b)
    ensures hasOppositeSign_postcond(a, b, result)
{
    // <vc-code>
    let result = false; assume(false); result
    // </vc-code>
}
// </vc-task>

fn main() {}
} // verus!
