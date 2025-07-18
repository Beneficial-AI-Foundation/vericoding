use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == k * k + 1,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == k * k + 1,
        /* code modified by LLM (iteration 3): added decreases clause to prove loop termination */
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 3): added bounds checking and overflow prevention */
        let i_i32 = i as i32;
        assert(i_i32 >= 0);
        assert(i_i32 < N);
        assert(i_i32 <= 46340); // sqrt(2^31 - 1) to prevent i32 overflow in multiplication
        let i_squared = i_i32 * i_i32;
        assert(i_squared >= 0);
        assert(i_squared <= 2147483646); // 2^31 - 2 to ensure +1 doesn't overflow
        let value = i_squared + 1;
        a.set(i, value);
        i += 1;
    }
}
}