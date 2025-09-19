// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_of_digits(x: nat) -> nat
    decreases x
{
    if x == 0 { 0 } else { (x % 10) + sum_of_digits(x / 10) }
}

spec fn is_sum_divisible_by(x: nat, d: nat) -> bool
{
    (sum_of_digits(x) % d) == 0
}
// </vc-helpers>

// <vc-spec>
fn count_sum_divisible_by(n: usize, d: usize) -> (result: usize)
    requires d > 0,
    ensures 
        result <= n,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}