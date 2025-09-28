// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
fn zero() -> u32 { 0 }
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
    0u32
}
// </vc-code>

}
fn main() {}