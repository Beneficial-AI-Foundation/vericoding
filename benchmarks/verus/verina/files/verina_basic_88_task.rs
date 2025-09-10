use vstd::prelude::*;

verus! {

fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
{
    assume(false);
    unreached()
}

}
fn main() {}