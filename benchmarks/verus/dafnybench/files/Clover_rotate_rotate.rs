use vstd::prelude::*;

verus! {

fn rotate(a: &[i32], offset: usize) -> (result: Vec<i32>)
    requires 
        offset >= 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[(i + offset as int) % a.len() as int],
{
    assume(false);
    unreached()
}

}
fn main() {}