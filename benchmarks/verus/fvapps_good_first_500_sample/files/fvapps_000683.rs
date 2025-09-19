// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn will_pipe_burst(m: nat, tc: int, th: int) -> (result: bool)
    requires tc <= th,
    ensures 
        ((th - tc) % 3 != 0) ==> result == true,
        ((th - tc) % 3 == 0) ==> result == ((th - tc) / 3 > m),
        (tc == th) ==> result == false
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // #guard_msgs in
    // #eval will_pipe_burst 4 5 10

    // #guard_msgs in  
    // #eval will_pipe_burst 2 2 5

    // #guard_msgs in
    // #eval will_pipe_burst 1 1 7
}