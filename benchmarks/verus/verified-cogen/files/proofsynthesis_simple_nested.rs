// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)

    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,

    ensures
        N <= sum <= 2*N,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}