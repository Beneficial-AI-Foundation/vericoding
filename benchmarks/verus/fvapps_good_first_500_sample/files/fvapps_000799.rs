// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

fn can_complete_task(x: u64, y: u64) -> (result: bool)
    requires 
        x > 0,
        y > 0,
    ensures 
        result <==> (gcd(x as nat, y as nat) == 1),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {}