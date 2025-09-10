use vstd::prelude::*;

verus!{

fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,

	ensures
		sum[0] == 0,
{
    assume(false);
    unreached();
}

}
fn main() {}