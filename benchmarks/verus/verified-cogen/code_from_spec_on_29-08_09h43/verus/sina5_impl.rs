use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_arithmetic_bounds(N: i32, i: i32)
    requires N > 0, N < 1000, 0 <= i < N
    ensures 2 * N + 1 <= i32::MAX
{
    assert(N < 1000);
    assert(2 * N < 2000);
    assert(2 * N + 1 < 2001);
    assert(2001 <= i32::MAX);
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
		forall |k:int| 0 <= k < N ==> a[k] == 2 * N + 1,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    /* code modified by LLM (iteration 5): lemma call in proof block */
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == 2 * N + 1,
        decreases N - i,
    {
        proof {
            lemma_arithmetic_bounds(N, i);
        }
        a[i as usize] = 2 * N + 1;
        i = i + 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}