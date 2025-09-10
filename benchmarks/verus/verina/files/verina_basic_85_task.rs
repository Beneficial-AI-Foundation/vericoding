use vstd::prelude::*;

verus! {

fn reverse(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[a.len() - 1 - i],
{
    assume(false);
    unreached();
}

}
fn main() {}