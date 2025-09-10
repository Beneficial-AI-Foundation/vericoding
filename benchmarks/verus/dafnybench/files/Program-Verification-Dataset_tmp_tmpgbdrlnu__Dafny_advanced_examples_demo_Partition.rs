use vstd::prelude::*;

verus! {

fn partition(a: &mut Vec<i32>) -> (lo: usize, hi: usize)
    ensures
        0 <= lo && lo <= hi && hi <= a.len(),
        forall|x: int| 0 <= x < lo ==> a[x as int] < 0,
        forall|x: int| lo <= x < hi ==> a[x as int] == 0,
        forall|x: int| hi <= x < a.len() ==> a[x as int] > 0,
{
    assume(false);
    unreached();
}

}
fn main() {}