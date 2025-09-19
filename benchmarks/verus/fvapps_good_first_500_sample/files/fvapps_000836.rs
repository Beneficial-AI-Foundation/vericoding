// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_last_laddu(n: nat) -> (result: nat)
    requires n > 0,
    ensures 
        0 < result && result <= n,
        2 * result > n,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // #eval find_last_laddu 1
    // #eval find_last_laddu 5  
    // #eval find_last_laddu 8
}