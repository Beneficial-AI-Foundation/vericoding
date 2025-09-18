// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to while loop */
fn flip_row(row: &Vec<f32>) -> (flipped: Vec<f32>)
    requires
        row.len() > 0,
    ensures
        flipped.len() == row.len(),
        forall|j: int| 0 <= j < flipped.len() as int ==> 
            flipped@[j] == row@[(row.len() as int - 1 - j)],
{
    let mut flipped_row = Vec::new();
    let n = row.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == row.len(),
            i <= n,
            flipped_row.len() == i,
            forall|k: int| 0 <= k < i as int ==> 
                flipped_row@[k] == row@[(n as int - 1 - k)],
        decreases n - i,
    {
        let val = row[n - 1 - i];
        flipped_row.push(val);
        i = i + 1;
    }
    flipped_row
}
// </vc-helpers>

// <vc-spec>
fn fliplr(m: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() > 0,
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[i].len(),
        forall|i: int, j: int| #![trigger result[i][j]] 0 <= i < result.len() && 0 <= j < result[i].len() ==>
            result[i][j] == m[i][(m[i].len() - 1 - j as usize) as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added decreases clause to while loop */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result@[k].len() == m@[k].len(),
            forall|k: int, l: int| #![trigger result@[k]@[l]] 0 <= k < i as int && 0 <= l < result@[k].len() as int ==>
                result@[k]@[l] == m@[k]@[(m@[k].len() as int - 1 - l)],
        decreases m.len() - i,
    {
        let row = &m[i];
        let flipped_row = flip_row(row);
        result.push(flipped_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}