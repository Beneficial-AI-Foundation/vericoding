// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_ways_to_climb(n: nat) -> (result: nat)
    requires n > 0,
    ensures 
        result > 0,
        result <= n,
        result >= (n + 1) / 2,
        (n == 1) ==> (result == 1),
        (n == 2) ==> (result == 2),
        (n > 0 && n % 2 == 0) ==> (result == n / 2 + 1),
        (n > 0 && n % 2 == 1) ==> (result == (n - 1) / 2 + 1),
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
    // Assurance level: guarded_and_plausible

    // #guard_msgs in
    // #eval count_ways_to_climb 3

    // #guard_msgs in
    // #eval count_ways_to_climb 4

    // #guard_msgs in
    // #eval count_ways_to_climb 5
}