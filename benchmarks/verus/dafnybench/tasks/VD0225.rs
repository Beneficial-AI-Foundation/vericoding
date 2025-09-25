// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32,
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}