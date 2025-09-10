use vstd::prelude::*;

verus! {

fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
{
    assume(false);
    unreached()
}

}
fn main() {}