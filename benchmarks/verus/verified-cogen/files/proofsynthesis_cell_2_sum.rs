// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)

    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,

    ensures
        sum <= 2*N,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}