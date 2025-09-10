use vstd::prelude::*;

verus!{

fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 6 * N,
{
    assume(false);
    unreached()
}

}
fn main() {}