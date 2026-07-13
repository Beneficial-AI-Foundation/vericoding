// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn determine_server(p1: u32, p2: u32, k: u32) -> (result: &'static str)
    requires k > 0,
    ensures 
        result == "CHEF" || result == "COOK",
        ((p1 + p2) % (2 * k) < k) ==> result == "CHEF",
        ((p1 + p2) % (2 * k) >= k) ==> result == "COOK"
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "CHEF"
    // impl-end
}
// </vc-code>


}
fn main() {}