use vstd::prelude::*;

verus!{

// <vc-helpers>
fn lemma_arithmetic_bounds(N: i32)
    requires N > 0, N < 1000
    ensures N + 2 <= i32::MAX
{
}
// </vc-helpers>

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
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    /* code modified by LLM (iteration 5): cast N to usize for bounds and operations */
    while i < N
        invariant
            0 <= i <= N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == N + 2,
        decreases N - i,
    {
        /* code modified by LLM (iteration 5): ensure arithmetic safety with explicit bounds check */
        proof {
            lemma_arithmetic_bounds(N);
        }
        b.set(i as usize, N + 2);
        i += 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}