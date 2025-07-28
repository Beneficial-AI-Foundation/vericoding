use vstd::prelude::*;

verus!{
//IMPL myfun
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] == 5 * N,
	// post-conditions-end
{
    sum.set(0, 5 * (N as i32));
}
}

fn main() {}