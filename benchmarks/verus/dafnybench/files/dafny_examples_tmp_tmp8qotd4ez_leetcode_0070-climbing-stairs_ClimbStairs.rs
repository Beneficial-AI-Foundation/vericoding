// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}