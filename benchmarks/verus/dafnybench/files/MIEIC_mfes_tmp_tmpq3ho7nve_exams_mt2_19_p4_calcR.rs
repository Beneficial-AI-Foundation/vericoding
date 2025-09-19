// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn R(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        0nat 
    } else if R((n-1) as nat) > n { 
        (R((n-1) as nat) - n) as nat
    } else { 
        (R((n-1) as nat) + n) as nat
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calcR(n: u8) -> (r: u8)
    ensures r as nat == R(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}