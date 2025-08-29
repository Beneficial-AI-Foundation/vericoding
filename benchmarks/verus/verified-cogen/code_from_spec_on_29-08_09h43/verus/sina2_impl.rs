use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_cast_bounds(i: i32, N: i32)
    requires 0 <= i < N, N < 1000
    ensures 0 <= i as usize, i as usize < N as usize
{}

proof fn lemma_no_overflow(N: i32)
    requires N > 0, N < 1000
    ensures N + 1 <= i32::MAX
{}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    /* code modified by LLM (iteration 5): added overflow check and cast bounds */
    proof {
        lemma_no_overflow(N);
    }
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == N + 1,
        decreases N - i
    {
        /* code modified by LLM (iteration 5): added cast bounds proof */
        proof {
            lemma_cast_bounds(i, N);
        }
        a.set(i as usize, N + 1);
        i += 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}