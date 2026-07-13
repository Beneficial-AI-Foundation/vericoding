// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_perfect_teams(c: nat, m: nat, x: nat) -> (result: nat)
    ensures
        result >= 0,
        result <= c,
        result <= m,
        result * 3 <= c + m + x,
        result == vstd::math::min(vstd::math::min(c as int, m as int), (c + m + x) as int / 3) as nat
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

    // assert_eq!(max_perfect_teams(1, 1, 1), 1);
    // assert_eq!(max_perfect_teams(3, 6, 0), 3);
    // assert_eq!(max_perfect_teams(0, 0, 0), 0);
    // assert_eq!(max_perfect_teams(0, 1, 1), 0);
}