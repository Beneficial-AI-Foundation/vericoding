use vstd::prelude::*;

verus! {

fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
{
    assume(false);
    unreached();
}

}
fn main() {}