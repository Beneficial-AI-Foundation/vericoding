use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, N: u32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] % 2 == N % 2,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases N - i,
    {
        /* code modified by LLM (iteration 4): create value that preserves modulo 2 property */
        let value = if N % 2 == 0 { 0i32 } else { 1i32 };
        a.set(i as usize, value);
        /* code modified by LLM (iteration 4): assert that the newly set element satisfies the modulo property */
        assert(a[i as int] % 2 == N % 2);
        i += 1;
    }
}
}