// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sum_multiples_of_ten_spec(n: nat) -> nat
    decreases n
{
    if n < 10 {
        0
    } else {
        let k = n / 10;
        k * (k + 1) * 5
    }
}

fn sum_multiples_of_ten(n: nat) -> (result: nat)
    ensures
        result >= 0,
        result % 10 == 0,
        result == sum_multiples_of_ten_spec(n),
        (n == 0 || n < 10) ==> result == 0
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

    // Test cases:
    // assert(sum_multiples_of_ten(10) == 10);
    // assert(sum_multiples_of_ten(20) == 30);
    // assert(sum_multiples_of_ten(100) == 550);
}