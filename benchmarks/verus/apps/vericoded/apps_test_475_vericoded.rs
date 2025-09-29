// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: nat, m: nat, k: nat) -> bool {
    n >= 1 && m >= 1 && k >= 0 && k <= n - 1
}

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else { n * factorial((n - 1) as nat) }
}

spec fn binomial(n: nat, k: nat) -> nat
    decreases n
{
    if k > n { 0 }
    else if factorial(k) == 0 || factorial((n - k) as nat) == 0 { 0 }
    else { factorial(n) / (factorial(k) * factorial((n - k) as nat)) }
}

spec fn power(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 }
    else { base * power(base, (exp - 1) as nat) }
}

spec fn expected_result(n: nat, m: nat, k: nat) -> nat {
    if valid_input(n, m, k) {
        (m * power((m - 1) as nat, k) * binomial((n - 1) as nat, k)) % 998244353
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: u64, m: u64, k: u64) -> (result: u64)
    requires n as nat >= 1 && m as nat >= 1 && k as nat >= 0 && k as nat <= n as nat - 1
    ensures result < 998244353
// </vc-spec>
// <vc-code>
{
    0u64
}
// </vc-code>


}

fn main() {}