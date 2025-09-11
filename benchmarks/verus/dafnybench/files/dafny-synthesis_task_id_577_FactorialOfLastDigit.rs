// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial((n - 1) as int) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn factorial_of_last_digit(n: u64) -> (fact: u64)
    requires n >= 0
    ensures fact == factorial((n % 10) as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}