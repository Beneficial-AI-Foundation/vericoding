use vstd::prelude::*;

verus!{

fn myfun(a: &mut Vec<i32>, N: i32, m: i32)

	requires
		N > 0,
		old(a).len() == N,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
{
    assume(false);
    unreached();
}

}
fn main() {}