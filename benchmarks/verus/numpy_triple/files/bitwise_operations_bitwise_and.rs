use vstd::prelude::*;

verus! {

fn bitwise_and(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x1[i],
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x2[i],
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
{
    assume(false);
    unreached()
}

}
fn main() {}