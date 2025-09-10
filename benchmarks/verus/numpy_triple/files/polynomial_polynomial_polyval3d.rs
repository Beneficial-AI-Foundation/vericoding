use vstd::prelude::*;

verus! {

fn polyval3d(
    x: Vec<f32>, 
    y: Vec<f32>, 
    z: Vec<f32>, 
    c: Vec<Vec<Vec<f32>>>
) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
    ensures 
        result.len() == x.len(),
        forall|p: int| 0 <= p < x.len() ==> 
            exists|val: f32| result[p] == val &&
            (c.len() == 1 && c[0].len() == 1 && c[0][0].len() == 1 ==> 
             val == c[0][0][0])
{
    assume(false);
    unreached();
}

}
fn main() {}