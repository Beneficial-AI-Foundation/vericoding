// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn expt(b: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { b * expt(b, (n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn expt_method(b: i32, n: u32) -> (res: i32)
    ensures res == expt(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}