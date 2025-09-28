// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn true_() -> (result: bool)
    ensures 
        result == true,
        !result == false
// </vc-spec>
// <vc-code>
{
    true
}
// </vc-code>

}
fn main() {}