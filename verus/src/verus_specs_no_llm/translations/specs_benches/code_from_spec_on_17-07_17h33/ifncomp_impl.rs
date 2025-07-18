use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> c[k] == N + k * k * k,
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            0 <= i <= N,
            c.len() == N,
            forall |k:int| 0 <= k < i ==> c[k] == N + k * k * k,
        /* code modified by LLM (iteration 4): fixed decreases clause for proper termination */
        decreases N as usize - i,
    {
        let k = i as i32;
        /* code modified by LLM (iteration 4): use int type for arithmetic to avoid overflow issues */
        let k_int = k as int;
        let n_int = N as int;
        
        /* code modified by LLM (iteration 4): calculate k_cubed using int arithmetic */
        let k_squared_int = k_int * k_int;
        let k_cubed_int = k_squared_int * k_int;
        let result_int = n_int + k_cubed_int;
        
        /* code modified by LLM (iteration 4): add proper bounds assertions for int to i32 conversion */
        assert(k_int >= 0);
        assert(k_int < n_int);
        assert(k_squared_int >= 0);
        assert(k_cubed_int >= 0);
        assert(result_int >= i32::MIN);
        assert(result_int <= i32::MAX);
        
        c.set(i, result_int as i32);
        i += 1;
    }
}
}