// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 
        gcd(sub(m, n), n)
    } else {
        gcd(m, sub(n, m))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn Product(m: u64, n: u64) -> (res: u64)
ensures res == m * n
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}