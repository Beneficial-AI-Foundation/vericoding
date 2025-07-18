use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> b[k] == k*k + k + 1,
{
    let mut i: usize = 0;
    /* code modified by LLM (iteration 4): Added stronger invariants and bounds to prevent overflow */
    while i < N as usize
        invariant
            i <= N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == k*k + k + 1,
            i < i32::MAX,
            N < i32::MAX,
        decreases N as usize - i,
    {
        let k = i as i32;
        /* code modified by LLM (iteration 4): Use i64 for intermediate calculation with proper overflow bounds */
        let k_wide = k as i64;
        /* code modified by LLM (iteration 4): Assert bounds before arithmetic operations */
        assert(k_wide >= 0);
        assert(k_wide < i32::MAX as i64);
        assert(k_wide * k_wide <= i64::MAX - k_wide - 1);
        let result_wide = k_wide * k_wide + k_wide + 1;
        /* code modified by LLM (iteration 4): Add explicit bounds proof for cast safety */
        assert(result_wide >= 1);
        assert(result_wide <= i32::MAX as i64);
        let result = result_wide as i32;
        b.set(i, result);
        i += 1;
    }
}
}