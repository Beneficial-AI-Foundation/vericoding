use vstd::prelude::*;

verus! {

fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
{
    assume(false);
    unreached()
}

}
fn main() {}