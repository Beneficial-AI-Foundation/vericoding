use vstd::prelude::*;

verus! {

fn numpy_bitwise_not(x: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == -(x[i] + 1)
{
    assume(false);
    unreached()
}

}
fn main() {}