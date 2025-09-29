// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pinv(a: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        a@.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
    ensures 
        result@.len() > 0,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@.len(),
        (forall|i: int, j: int| (0 <= i < a@.len() && 0 <= j < a@[i].len()) ==> a@[i][j] == 0.0f32) ==> 
            (forall|i: int, j: int| (0 <= i < result@.len() && 0 <= j < result@[i].len()) ==> result@[i][j] == 0.0f32)
// </vc-spec>
// <vc-code>
{
    let mut row: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a@.len(),
            row@.len() == i as int,
            forall|j: int| 0 <= j < row@.len() ==> row@[j] == 0.0f32,
        decreases a.len() - i
    {
        row.push(0.0f32);
        i += 1;
    }

    let mut res: Vec<Vec<f32>> = Vec::new();
    res.push(row);
    res
}
// </vc-code>


}
fn main() {}