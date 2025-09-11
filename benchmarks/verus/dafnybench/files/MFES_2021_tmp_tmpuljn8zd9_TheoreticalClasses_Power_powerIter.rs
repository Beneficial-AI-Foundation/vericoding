// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}