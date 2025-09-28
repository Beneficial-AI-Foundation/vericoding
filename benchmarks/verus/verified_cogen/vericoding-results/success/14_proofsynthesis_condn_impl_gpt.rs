// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): minimum over mathematical integers */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
/* helper modified by LLM (iteration 3): predicate to express in-bounds indices for specs */
spec fn in_bounds(i: int, n: int) -> bool { 0 <= i && i < n }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, N: i32, m: i32)

	requires
		N > 0,
		old(a).len() == N,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement loop setting all entries to N and fix forall proof via case analysis on antecedent */
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i && i <= N,
            a.len() as int == N as int,
            forall |k:int| 0 <= k && k < i ==> a@[k] <= N
        decreases (N - i) as int
    {
        let j: i32 = i;
        proof {
            assert(0 <= j && j < N);
            assert(a.len() as int == N as int);
            assert(0 <= j && j < a.len() as int);
        }
        a[j as usize] = N;
        i = j + 1;
        proof {
            assert forall |k:int| 0 <= k && k < i ==> a@[k] <= N by {
                if 0 <= k && k < i {
                    if k < j {
                        assert(0 <= k && k < j);
                        assert(a@[k] <= N);
                    } else {
                        assert(i == j + 1);
                        assert(k < j + 1);
                        assert(j <= k); // from !(k < j)
                        assert(k <= j); // from k < j + 1
                        assert(k == j);
                        assert(0 <= j && j < a.len() as int);
                        assert(0 <= k && k < a.len() as int);
                        assert(a@[k] == N);
                    }
                }
            }
        }
    }
}
// </vc-code>

}
fn main() {}