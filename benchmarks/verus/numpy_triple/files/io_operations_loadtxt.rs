use vstd::prelude::*;

verus! {

fn loadtxt(filename: Seq<char>, delimiter: Seq<char>, skiprows: usize, rows: usize, cols: usize) -> (result: Vec<Vec<f64>>)
    requires 
        rows > 0,
        cols > 0,
        filename.len() > 0,
    ensures
        result.len() == rows,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == cols,
{
    assume(false);
    unreached();
}

}
fn main() {}