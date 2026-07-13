// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_first_last_digit(n: nat) -> (result: nat)
    requires n > 0,
    ensures 
        result >= 0 && result <= 18,
        n <= 9 ==> result == n + n
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

    // println!("{}", sum_first_last_digit(1234));
    // println!("{}", sum_first_last_digit(124894));
    // println!("{}", sum_first_last_digit(242323));
}