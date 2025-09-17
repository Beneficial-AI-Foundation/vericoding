// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn modp(n: int, p: int) -> (result: int)
    requires 
        n >= 0 && p > 0,
    ensures 
        result >= 0 && result < p,
        result == power(2, n as nat) % p,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}