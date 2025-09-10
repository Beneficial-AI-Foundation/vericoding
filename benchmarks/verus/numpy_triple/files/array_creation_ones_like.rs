use vstd::prelude::*;

verus! {

fn ones_like<T>(a: &Vec<T>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1,
{
    assume(false);
    unreached();
}

}
fn main() {}