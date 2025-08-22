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
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 2): added bounds checking and proper invariants for array access */
    while i < N as usize
        invariant
            i <= N as usize,
            total <= 2 * (i as i32),
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
        decreases N as usize - i
    {
        /* code modified by LLM (iteration 2): added bounds check before array access */
        if i < a.len() && i < b.len() {
            let val_a = if a[i] > 1 { 1 } else if a[i] < 0 { 0 } else { a[i] };
            let val_b = if b[i] > 1 { 1 } else if b[i] < 0 { 0 } else { b[i] };
            total = total + val_a + val_b;
        }
        i = i + 1;
    }
    
    sum.set(0, total);
}
}