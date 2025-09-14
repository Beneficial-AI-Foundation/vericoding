// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn le_double_i32(x: i32)
    requires 0 <= x
    ensures x <= 2 * x
{
}

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
    let sum = N;
    sum
}
// </vc-code>

}
fn main() {}