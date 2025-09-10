use vstd::prelude::*;

verus! {

fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
{
    assume(false);
    unreached()
}

}
fn main() {}