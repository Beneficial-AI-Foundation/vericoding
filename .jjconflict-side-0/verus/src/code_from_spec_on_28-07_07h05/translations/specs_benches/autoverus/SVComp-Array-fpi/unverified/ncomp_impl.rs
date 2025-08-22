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
    /* code modified by LLM (iteration 4): improved loop invariants and bounds checking */
    while i < N as usize
        invariant
            0 <= i <= N,
            c.len() == N,
            forall |k:int| 0 <= k < i ==> c[k] == N + k * k * k,
            N >= 0,
        decreases N as usize - i
    {
        let k = i as i32;
        
        /* code modified by LLM (iteration 4): use proof block for spec arithmetic */
        proof {
            let k_spec = k as int;
            let k_cubed_spec = k_spec * k_spec * k_spec;
            let result_spec = N as int + k_cubed_spec;
        }
        
        /* code modified by LLM (iteration 4): compute result using regular arithmetic */
        let k_cubed = k * k * k;
        let result = N + k_cubed;
        
        c.set(i, result);
        i += 1;
    }
}
}