// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bulb_switch(n: i32) -> (result: i32)
    ensures 
        n >= 0 ==> (result >= 0 && result <= n),
        n < 0 ==> result == -1,
        n == 0 ==> result == 0
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
    // Apps difficulty: interview
    // Assurance level: unguarded

    // #eval bulb_switch 3 should return 1
    // #eval bulb_switch 0 should return 0  
    // #eval bulb_switch 4 should return 2
}