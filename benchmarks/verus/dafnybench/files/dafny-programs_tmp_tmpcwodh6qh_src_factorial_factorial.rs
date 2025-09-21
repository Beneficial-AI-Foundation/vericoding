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
fn factorial(n: u8) -> (res: u8)
    requires n as nat <= 12
    ensures res as nat == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}