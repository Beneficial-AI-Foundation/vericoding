// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
// </vc-spec>
// <vc-code>
{
    let n = N as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            n == N as usize,
            forall |k: int| 0 <= k < i ==> b[k as int] == N + 2,
        decreases n - i,
    {
        b.set(i, (N + 2) as i32);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}