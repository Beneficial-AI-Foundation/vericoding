use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == k * k,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            /* code modified by LLM (iteration 3): strengthened invariant to ensure it holds at loop end */
            forall |k:int| 0 <= k < i as int ==> a[k] == k * k,
            /* code modified by LLM (iteration 3): added bound to prevent overflow */
            i < a.len() ==> (i as i32) * (i as i32) <= i32::MAX,
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 3): added overflow check and proper arithmetic */
        let i_i32 = i as i32;
        assert(i_i32 * i_i32 <= i32::MAX); // This should hold from invariant
        let square = i_i32 * i_i32;
        a.set(i, square);
        /* code modified by LLM (iteration 3): assert to help prove invariant maintenance */
        assert(forall |k:int| 0 <= k < (i + 1) as int ==> a[k] == k * k);
        i += 1;
    }
}
}