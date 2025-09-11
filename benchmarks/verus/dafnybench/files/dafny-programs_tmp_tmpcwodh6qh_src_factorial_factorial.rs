// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}