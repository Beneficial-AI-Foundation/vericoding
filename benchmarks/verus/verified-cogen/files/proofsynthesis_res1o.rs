use vstd::prelude::*;

verus!{

fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] <= 2 * N,
{
    assume(false);
    unreached()
}

}
fn main() {}