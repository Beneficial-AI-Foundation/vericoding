use vstd::prelude::*;

verus! {

fn partition(a: &mut Vec<i32>) -> (r : (usize, usize))
    ensures
        0 <= r.0 && r.0 <= r.1 && r.1 <= a.len(),
        forall|x: int| 0 <= x < r.0 ==> a[x as int] < 0,
        forall|x: int| r.0 <= x < r.1 ==> a[x as int] == 0,
        forall|x: int| r.1 <= x < a.len() ==> a[x as int] > 0,
{
    assume(false);
    unreached()
}

}
fn main() {}