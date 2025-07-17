use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> c[k] == N + k * k * k,
{
    // TODO: Remove this comment and implement the function body
}
}