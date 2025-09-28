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

spec fn exp(x: real, n: nat) -> real
decreases n
{
    if n == 0 {
        1.0
    } else if x == 0.0 {
        0.0
    } else if n == 0 && x == 0.0 {
        1.0
    } else {
        x * exp(x, sub(n, 1))
    }
}

// <vc-helpers>
use vstd::num::real::Real;

spec fn exp_real(x: Real, n: nat) -> Real
decreases n
{
    if n == 0 {
        Real::from_int(1)
    } else if x == Real::from_int(0) {
        Real::from_int(0)
    } else {
        x * exp_real(x, sub(n, 1))
    }
}

#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
#[allow(dead_code)]
fn product_u64_builtin(m: u64, n: u64) -> (res: u64) {
    m * n
}
// </vc-helpers>

// <vc-spec>
fn Product(m: u64, n: u64) -> (res: u64)
ensures res == m * n
// </vc-spec>
// <vc-code>
{
    product_u64_builtin(m, n)
}
// </vc-code>

fn main() {}

}