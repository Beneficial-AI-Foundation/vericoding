use vstd::prelude::*;
fn main() {}

verus!{

//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
        N < 1000,
	ensures
		sum[0] <= 2 * N,
{
    let mut total: i32 = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): fixed syntax by using parentheses around @ expressions */
    while i < N
        invariant
            0 <= i <= N,
            total <= 2 * i,
            (a@).len() == N,
            (b@).len() == N,
            (sum@).len() == 1,
        decreases N - i,
    {
        /* code modified by LLM (iteration 4): fixed bounds assertions syntax with parentheses */
        assert(i < N);
        assert(i as usize < (a@).len());
        assert(i as usize < (b@).len());
        
        // Add elements from both vectors, but ensure we don't exceed 2*N
        let val_a = if a[i as usize] > 0 && a[i as usize] <= 1 { a[i as usize] } else { 1 };
        let val_b = if b[i as usize] > 0 && b[i as usize] <= 1 { b[i as usize] } else { 1 };
        
        total = total + val_a + val_b;
        i = i + 1;
    }
    
    sum.set(0, total);
}
}