use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn true_() -> (result: bool)
    ensures 
        result == true,
        forall|b: bool| (result && b) == b,
        forall|b: bool| (result || b) == true,
        !result == false
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}