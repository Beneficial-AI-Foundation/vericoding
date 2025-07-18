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
		forall |k:int| 0 <= k < N ==> c[k] == k * k * k,
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            0 <= i <= N,
            c.len() == N,
            forall |k:int| 0 <= k < i ==> c[k] == k * k * k,
        /* code modified by LLM (iteration 4): added decreases clause to prove loop termination */
        decreases N as usize - i,
    {
        /* code modified by LLM (iteration 4): use int arithmetic to avoid overflow, then convert to i32 */
        let i_int = i as int;
        let cube_int = i_int * i_int * i_int;
        let cube = cube_int as i32;
        c.set(i, cube);
        i += 1;
    }
}
}