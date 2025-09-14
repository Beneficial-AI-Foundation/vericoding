// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added invariant to prevent overflow */
    let mut i: usize = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            forall|j: int| 0 <= j < i ==> a@[j] == 2,
            forall|j: int| i <= j < N ==> a@[j] == old(a)@[j],
        decreases N - i
    {
        a.set(i, 2);
        i = i + 1;
    }

    let mut total: i32 = 0;
    let mut k: usize = 0;
    while k < N
        invariant
            0 <= k <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000, // This invariant is needed to prove the absence of arithmetic overflow
            forall|j: int| 0 <= j < N ==> a@[j] == 2,
            total == 2 * (k as int),
        decreases N - k
    {
        total = total + a[k];
        k = k + 1;
    }

    sum.set(0, total);
}
// </vc-code>

}
fn main() {}