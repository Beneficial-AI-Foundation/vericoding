use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> b[k] == 5 * k * k + 5 * k + 1,
{
    let mut i: usize = 0;
    /* code modified by LLM (iteration 4): use i32 instead of int for executable code, add ghost variable for specification */
    while i < N as usize
        invariant
            i <= N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 5 * k * k + 5 * k + 1,
        decreases N as usize - i,
    {
        /* code modified by LLM (iteration 4): use i64 for intermediate calculations to prevent overflow */
        let k_i32 = i as i32;
        let k_i64 = i as i64;
        let result_i64 = 5i64 * k_i64 * k_i64 + 5i64 * k_i64 + 1i64;
        let result = result_i64 as i32;
        b.set(i, result);
        
        /* code modified by LLM (iteration 4): add ghost proof that the result satisfies the specification */
        proof {
            let k_ghost = i as int;
            assert(k_ghost == k_i32 as int);
            assert(result as int == 5 * k_ghost * k_ghost + 5 * k_ghost + 1);
        }
        
        i += 1;
    }
}
}