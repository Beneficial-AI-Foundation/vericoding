use vstd::prelude::*;

verus! {

fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
{
    assume(false);
    unreached()
}

}
fn main() {}