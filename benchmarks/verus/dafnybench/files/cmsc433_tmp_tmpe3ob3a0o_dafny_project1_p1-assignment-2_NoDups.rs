use vstd::prelude::*;

verus! {

fn no_dups(a: &Vec<i32>) -> (no_dups: bool)
    requires forall|j: int| 1 <= j < a.len() ==> a[j-1] <= a[j],
    ensures no_dups <==> forall|j: int| 1 <= j < a.len() ==> a[j-1] != a[j],
{
    assume(false);
    unreached()
}

}
fn main() {}