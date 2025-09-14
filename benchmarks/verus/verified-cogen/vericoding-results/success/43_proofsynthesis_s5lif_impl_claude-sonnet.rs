// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 6 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed invariant and assertion issues */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            total == 6 * (i as i32),
            a.len() == N,
            N < 1000,
            total <= 6 * N,
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(a.len() == N);
            assert(N < 1000);
            assert(i < N);
            assert(total + 6 <= 6 * N);
        }
        a.set(i, 6);
        total = total + 6;
        i = i + 1;
    }
    
    proof {
        assert(i == a.len());
        assert(total == 6 * (i as i32));
        assert(total == 6 * N);
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}