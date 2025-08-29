use vstd::prelude::*;

verus!{

// <vc-helpers>
fn lemma_index_bounds(i: i32, N: i32)
    requires 0 <= i < N, N < 1000
    ensures i as usize < usize::MAX
{
}

fn lemma_addition_bounds(N: i32)
    requires 0 < N < 1000
    ensures N + 1 <= i32::MAX
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i: i32 = 0;
    /* code modified by LLM (iteration 5): fixed function body placement and maintained proper loop invariants */
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N < 1000,
            forall |k:int| 0 <= k < i ==> a@[k] == N + 1,
        decreases N - i,
    {
        proof {
            lemma_addition_bounds(N);
            lemma_index_bounds(i, N);
        }
        a.set(i as usize, N + 1);
        i += 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}