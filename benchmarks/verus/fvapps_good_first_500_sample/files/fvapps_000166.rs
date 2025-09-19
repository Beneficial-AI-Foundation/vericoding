// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn integer_break(n: nat) -> (result: nat)
    requires n >= 2
    ensures 
        result > 0,
        n >= 4 ==> result >= n,
        n == 2 ==> result == 1,
        n == 3 ==> result == 2
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
    // Assurance level: guarded

    // #guard_msgs in
    // #eval integer_break 2

    // #guard_msgs in  
    // #eval integer_break 10

    // #guard_msgs in
    // #eval integer_break 8
}