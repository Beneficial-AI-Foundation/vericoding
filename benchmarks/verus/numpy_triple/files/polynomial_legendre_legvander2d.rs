use vstd::prelude::*;

verus! {

fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: usize, deg_y: usize) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x + 1) * (deg_y + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
{
    assume(false);
    unreached()
}

}
fn main() {}