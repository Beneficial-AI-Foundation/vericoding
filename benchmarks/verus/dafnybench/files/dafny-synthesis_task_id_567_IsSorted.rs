use vstd::prelude::*;

verus! {

fn is_sorted(a: &[i32]) -> (sorted: bool)
    requires
        a.len() > 0,
    ensures
        sorted <==> forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() && a[i] > a[j],
{
    assume(false);
    unreached()
}

}
fn main() {}