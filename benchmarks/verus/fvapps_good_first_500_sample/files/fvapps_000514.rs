// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn min_shots_to_find_x(n: nat, l: nat) -> nat
{
    if n == 1 {
        l
    } else if n == 2 {
        if l <= 4 { l } else { 4 }
    } else {
        l / (n + 1) + 1
    }
}

fn min_shots_to_find_x_impl(n: u32, l: u32) -> (result: u32)
    requires n > 0 && l > 0,
    ensures 
        result > 0,
        result <= l,
        n == 1 ==> result == l
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn single_bullet_shots(l: nat)
    requires l > 0,
    ensures min_shots_to_find_x(1, l) == l
{
    assume(false);
}

proof fn two_bullets_shots(l: nat) 
    requires l > 0,
    ensures min_shots_to_find_x(2, l) >= 1
{
    assume(false);
}

proof fn n_bullets_shots(n: nat, l: nat)
    requires n > 2 && l > 0,
    ensures min_shots_to_find_x(n, l) * (n + 1) >= l
{
    assume(false);
}

proof fn shots_always_positive(n: nat, l: nat)
    requires n > 0 && l > 0,
    ensures min_shots_to_find_x(n, l) > 0
{
    assume(false);
}

proof fn shots_less_than_length(n: nat, l: nat)
    requires n > 0 && l > 0,
    ensures min_shots_to_find_x(n, l) <= l
{
    assume(false);
}
// </vc-code>


}

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded

    // Example evaluations:
    // min_shots_to_find_x(1, 10) should return 10
    // min_shots_to_find_x(2, 10) should return 4
    // min_shots_to_find_x(3, 16) should return 4
}