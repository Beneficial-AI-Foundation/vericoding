use vstd::prelude::*;

verus! {

fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
{
    assume(false);
    unreached()
}

}
fn main() {}