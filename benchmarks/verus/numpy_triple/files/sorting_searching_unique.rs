use vstd::prelude::*;

verus! {

fn unique(ar: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        result.1.len() <= ar.len(),

        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i as int] <= result.1[j as int],

        forall|i: int, j: int| 0 <= i < result.1.len() && 0 <= j < result.1.len() && i != j ==> result.1[i as int] != result.1[j as int],
{
    assume(false);
    unreached();
}

}
fn main() {}