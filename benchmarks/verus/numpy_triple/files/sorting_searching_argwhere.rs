use vstd::prelude::*;

verus! {

fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices.len() ==> 
            indices[i] < a.len() && a[indices[i] as int] != 0.0,

        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] != indices[j],

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] < indices[j],
{
    assume(false);
    unreached()
}

}
fn main() {}