use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
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
            forall |k:int| 0 <= k < i ==> a[k] == (k + 1) * (k + 1),
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases N as usize - i
    {
        let val = ((i + 1) * (i + 1)) as i32;
        a.set(i, val);
        i += 1;
    }
}
}