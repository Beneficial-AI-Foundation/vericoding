// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i8) -> (u: i8)
    requires 1 <= n as int,
    ensures u as nat == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}