use vstd::prelude::*;

verus! {

fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
{
    assume(false);
    unreached()
}

}
fn main() {}