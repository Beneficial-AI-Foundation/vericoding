use vstd::prelude::*;

verus! {

fn legcompanion(c: Vec<f64>) -> (result: Vec<Vec<f64>>)
    requires 
        c.len() >= 2,
        c[c.len() - 1] != 0.0,
    ensures 
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() ==> 
            result[i][j] == result[j][i],
{
    assume(false);
    unreached()
}

}
fn main() {}