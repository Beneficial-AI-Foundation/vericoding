use vstd::prelude::*;


verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    // pre-conditions-start
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum[0] == 4 * N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N as int,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 4 * N);
}
// </vc-code>

}

fn main() {}