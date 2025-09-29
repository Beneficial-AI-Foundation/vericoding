// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec_vec_f64(v: Vec<Vec<f64>>) -> (res: Vec<Vec<f64>>)
    ensures
        res@ == v@,
{
    v
}
// </vc-helpers>

// <vc-spec>
fn as_series(arr: Vec<Vec<f64>>, trim: bool) -> (result: Vec<Vec<f64>>)
    requires 
        arr@.len() > 0,
        forall|i: int| 0 <= i < arr@.len() ==> arr@[i].len() > 0,
    ensures 
        result@.len() == arr@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            if !trim {
                result@[i].len() == arr@[i].len() &&
                forall|j: int| 0 <= j < arr@[i].len() ==> result@[i][j] == arr@[i][j]
            } else {
                forall|j: int| 0 <= j < result@[i].len() ==> {
                    result@[i][j] == arr@[i][j] || result@[i][j] == 0.0
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    id_vec_vec_f64(arr)
}
// </vc-code>

}
fn main() {}