// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn increment_or_decrement(n: i32) -> (result: i32)
    requires 0 <= n <= 1000,
    ensures 
        (n % 4 == 0) ==> (result == n + 1),
        (n % 4 != 0) ==> (result == n - 1),
        (result - n == 1) || (result - n == -1),
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
    // #guard_msgs in
    // #eval increment_or_decrement 5

    // #guard_msgs in  
    // #eval increment_or_decrement 8

    // #guard_msgs in
    // #eval increment_or_decrement 3
}