use vstd::prelude::*;

verus! {

fn laggrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c.len() ==> c[i].len() == c[j].len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < y.len() ==> 
            exists|val: f32| result[i][j] == val,
{
    assume(false);
    unreached();
}

}
fn main() {}