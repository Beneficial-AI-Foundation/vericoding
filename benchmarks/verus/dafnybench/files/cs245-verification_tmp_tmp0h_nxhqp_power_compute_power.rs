// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn power(a: int, n: nat) -> int
    recommends 0 <= a
    decreases n
{
    if n == 0 { 1 } else { a * power(a, (n - 1) as nat) }
}

fn compute_power(a: u64, n: u64) -> (s: u64)
    requires n >= 0 && a >= 0
    ensures s as int == power(a as int, n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}