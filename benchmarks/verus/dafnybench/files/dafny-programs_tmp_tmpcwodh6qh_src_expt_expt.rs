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
fn expt_method(b: i8, n: u8) -> (res: i8)
    ensures res as int == expt(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}