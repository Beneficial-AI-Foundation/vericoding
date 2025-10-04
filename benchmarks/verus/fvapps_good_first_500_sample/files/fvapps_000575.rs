// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sum_digits(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 10) + sum_digits(n / 10)
    }
}

fn find_jojo_aadhar(n: nat) -> (result: nat)
    ensures 
        sum_digits(result) % 10 == 0,
        result / 10 == n,
        0 <= result % 10 && result % 10 <= 9
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: unguarded */

}

fn main() {
    // #guard_msgs in
    // #eval find_jojo_aadhar 3

    // #guard_msgs in  
    // #eval find_jojo_aadhar 10

    // #guard_msgs in
    // #eval find_jojo_aadhar 42
}