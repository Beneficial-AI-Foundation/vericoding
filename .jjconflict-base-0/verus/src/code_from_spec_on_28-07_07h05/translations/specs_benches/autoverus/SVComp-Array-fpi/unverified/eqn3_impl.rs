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
    /* code modified by LLM (iteration 4): removed problematic N < 0x7fff invariant and fixed overflow issues */
    while i < N as usize
        invariant
            0 <= i <= N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 3*k*k + 3*k + 1,
        decreases N as usize - i,
    {
        let k = i as i32;
        /* code modified by LLM (iteration 4): use int arithmetic to avoid overflow, then convert safely */
        let k_int = k as int;
        let value_int = 3 * k_int * k_int + 3 * k_int + 1;
        
        /* code modified by LLM (iteration 4): assert the computed value fits in i32 range */
        assert(value_int >= i32::MIN && value_int <= i32::MAX);
        
        let value = value_int as i32;
        
        b.set(i, value);
        i = i + 1;
    }
}
}