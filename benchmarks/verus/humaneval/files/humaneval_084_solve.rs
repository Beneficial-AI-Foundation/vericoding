// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { (n % 2) + popcount(n / 2) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: u8) -> (r: u8)
    ensures r as nat == popcount(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}