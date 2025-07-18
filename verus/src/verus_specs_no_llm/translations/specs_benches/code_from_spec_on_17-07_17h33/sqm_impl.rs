use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == (k + 1) * (k + 1),
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == (k + 1) * (k + 1),
        /* code modified by LLM (iteration 3): added decreases clause for termination */
        decreases N as usize - i,
    {
        /* code modified by LLM (iteration 3): perform computation directly with i32 types */
        let i_i32 = i as i32;
        let val = (i_i32 + 1) * (i_i32 + 1);
        
        /* code modified by LLM (iteration 3): ghost assertion to help verify invariant maintenance */
        assert(val == (i as int + 1) * (i as int + 1));
        
        a.set(i, val);
        i += 1;
        
        /* code modified by LLM (iteration 3): added assertion to help verify invariant maintenance */
        assert(forall |k:int| 0 <= k < i ==> a[k] == (k + 1) * (k + 1));
    }
}
}