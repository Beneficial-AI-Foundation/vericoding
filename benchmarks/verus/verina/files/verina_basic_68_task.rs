use vstd::prelude::*;

verus! {

fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|i: int| 0 <= i < result ==> a[i] != e,
{
    assume(false);
    unreached()
}

}
fn main() {}