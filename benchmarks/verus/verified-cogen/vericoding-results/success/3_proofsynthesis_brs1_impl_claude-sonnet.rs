// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): bounds checking helpers */
spec fn safe_add_i32(a: i32, b: i32) -> bool {
    a <= i32::MAX - b && a >= i32::MIN - b
}

proof fn lemma_count_bounds(count: i32, i: int, N: i32)
    requires
        count <= i,
        i < N,
        count >= 0,
        N > 0,
    ensures
        count < N,
        safe_add_i32(count, 1),
{
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,

    ensures
        sum[0] <= N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added overflow checks and proper bounds */
    let mut count: i32 = 0;
    
    for i in 0..a.len()
        invariant
            count <= i,
            count >= 0,
            count <= N,
            a.len() == N,
    {
        if a[i] > 0 && count < N - 1 {
            count = count + 1;
        }
    }
    
    sum[0] = count;
}
// </vc-code>

}
fn main() {}