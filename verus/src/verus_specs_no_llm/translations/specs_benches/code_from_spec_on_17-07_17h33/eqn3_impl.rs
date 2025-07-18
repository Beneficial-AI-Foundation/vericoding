use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> b[k] == 3*k*k + 3*k + 1,
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            i <= N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 3*k*k + 3*k + 1,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases N as usize - i,
    {
        let k = i as i32;
        /* code modified by LLM (iteration 4): use i64 for intermediate calculations to prevent overflow */
        let k_64 = k as i64;
        let result_64 = 3 * k_64 * k_64 + 3 * k_64 + 1;
        let result = result_64 as i32;
        b.set(i, result);
        i += 1;
    }
}
}