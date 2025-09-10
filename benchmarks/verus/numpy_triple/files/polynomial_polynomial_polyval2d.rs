use vstd::prelude::*;

verus! {

fn polyval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() == c[0].len(),
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> exists|poly_val: f32| #[trigger] result[k] == poly_val,

        (c.len() == 1 && c[0].len() == 1) ==> 
            (forall|k: int| 0 <= k < result.len() ==> result[k] == c[0][0]),

        (forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j] == 0.0f32) ==> 
            (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32),

        forall|k: int| 0 <= k < result.len() && x[k] == 0.0f32 && y[k] == 0.0f32 ==> 
            result[k] == c[0][0],
{
    assume(false);
    unreached()
}

}
fn main() {}