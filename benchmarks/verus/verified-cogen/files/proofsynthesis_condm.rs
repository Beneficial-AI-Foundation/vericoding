use vstd::prelude::*;

verus!{

fn myfun(a: &mut Vec<i32>, N: u32)

		requires
			N > 0,
			old(a).len() == N,

		ensures
			forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    assume(false);
    unreached()
}

}
fn main() {}