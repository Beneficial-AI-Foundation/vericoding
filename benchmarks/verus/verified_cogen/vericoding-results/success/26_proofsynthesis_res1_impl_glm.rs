// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
        N < 1000,

	ensures
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed #[verifier::truncate] syntax */
    let mut count: i32 = 0;
    for i in 0..(N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            0 <= count <= #[verifier::truncate](i as i32),
    {
        let sum_i64 = a[i] as i64 + b[i] as i64;
        if sum_i64 > 0 {
            count += 1;
        }
    }
    sum[0] = count;
}
// </vc-code>

}
fn main() {}