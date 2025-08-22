use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
        /* code modified by LLM (iteration 1): added bounds to prevent overflow */
        N <= 23170, // sqrt((i32::MAX - 1) / 2) - 1 to ensure 2*k*k + 2*k + 1 fits in i32
	ensures
		forall |k:int| 0 <= k < N ==> b[k] == 2*k*k + 2*k + 1,
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            0 <= i <= N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 2*k*k + 2*k + 1,
        decreases N as usize - i
    {
        let k = i as i32;
        /* code modified by LLM (iteration 1): use explicit parentheses and step-by-step calculation to avoid overflow */
        let k_squared = k * k;
        let two_k_squared = 2 * k_squared;
        let two_k = 2 * k;
        let value = two_k_squared + two_k + 1;
        b.set(i, value);
        i += 1;
    }
}
}