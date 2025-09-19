// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn nth_person_gets_nth_seat(n: nat) -> int {
    if n == 1 {
        1
    } else if n > 1 {
        0
    } else {
        0
    }
}

proof fn prob_bounds(n: nat)
    requires n > 0,
    ensures 
        0 <= nth_person_gets_nth_seat(n) && nth_person_gets_nth_seat(n) <= 1,
{
    assume(false);
}

proof fn non_first_person_prob(n: nat)
    requires n > 1,
    ensures nth_person_gets_nth_seat(n) == 0,
{
    assume(false);
}

proof fn first_person_prob()
    ensures nth_person_gets_nth_seat(1) == 1,
{
    assume(false);
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // #guard_msgs in
    // #eval nth_person_gets_nth_seat 1

    // #guard_msgs in
    // #eval nth_person_gets_nth_seat 2

    // #guard_msgs in
    // #eval nth_person_gets_nth_seat 100
}