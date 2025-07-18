use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> b[k] == 2*k*k + 2*k + 1,
{
    let mut i: usize = 0;
    /* code modified by LLM (iteration 4): improved loop invariants and bounds */
    while i < N as usize
        invariant
            0 <= i <= N,
            N > 0,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 2*k*k + 2*k + 1,
        decreases N as usize - i,
    {
        let k = i as i32;
        /* code modified by LLM (iteration 4): use safer arithmetic computation to avoid overflow */
        let k_squared = k * k;
        let two_k_squared = 2 * k_squared;
        let two_k = 2 * k;
        let result = two_k_squared + two_k + 1;
        b.set(i, result);
        i += 1;
    }
}
}