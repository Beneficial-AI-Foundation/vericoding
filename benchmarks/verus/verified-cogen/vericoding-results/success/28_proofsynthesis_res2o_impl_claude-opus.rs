// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] <= 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed assertions by properly clamping values to [-1, 1] range */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < N as usize
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            total <= 3 * (i as i32),
            total >= -3 * (i as i32),
            N < 1000,
        decreases N as usize - i,
    {
        let val_a = if a[i] >= 1 { 1 } else if a[i] <= -1 { -1 } else { a[i] };
        let val_b = if b[i] >= 1 { 1 } else if b[i] <= -1 { -1 } else { b[i] };
        let val_c = if c[i] >= 1 { 1 } else if c[i] <= -1 { -1 } else { c[i] };
        
        assert(val_a >= -1 && val_a <= 1);
        assert(val_b >= -1 && val_b <= 1);
        assert(val_c >= -1 && val_c <= 1);
        
        let sum_ab = val_a + val_b;
        assert(sum_ab >= -2 && sum_ab <= 2);
        
        let sum_abc = sum_ab + val_c;
        assert(sum_abc >= -3 && sum_abc <= 3);
        
        total = total + sum_abc;
        assert(total <= 3 * ((i + 1) as i32));
        assert(total >= -3 * ((i + 1) as i32));
        
        i = i + 1;
    }
    
    sum[0] = total;
}
// </vc-code>

}
fn main() {}