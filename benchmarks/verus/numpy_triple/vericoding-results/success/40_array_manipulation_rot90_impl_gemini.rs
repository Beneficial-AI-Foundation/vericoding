// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed compilation error by adding explicit type annotations for `Vec::new()`. */
fn rotate_once(m: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() == m.len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m.len(),
        forall|i: int, j: int|
            0 <= i < m.len() && 0 <= j < m.len() ==> 
            result[i][j] == m[m.len() as int - 1 - j][i],
{
    let n = m.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            m.len() == n,
            forall|k: int| 0 <= k < m.len() ==> m[k].len() == m.len(),
            result.len() == i,
            forall|row: int| 0 <= row < i ==> (
                result[row].len() == n &&
                forall|col: int| 0 <= col < n ==> 
                    result[row][col] == m[n as int - 1 - col][row]
            ),
        decreases n - i
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                i < n,
                m.len() == n,
                forall|k: int| 0 <= k < m.len() ==> m[k].len() == m.len(),
                new_row.len() == j,
                forall|col: int| 0 <= col < j ==> 
                    new_row[col] == m[n as int - 1 - col][i as int],
            decreases n - j
        {
            new_row.push(m[n - 1 - j][i]);
            j = j + 1;
        }
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn rot90(m: Vec<Vec<f32>>, k: i32) -> (result: Vec<Vec<f32>>)
    requires
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() == m.len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): No changes as logic seems sound; focusing on fixing helper function. */
    let n = m.len();
    let mut current_m = m;
    let num_rotations = (k % 4 + 4) % 4;

    let mut i: i32 = 0;
    while i < num_rotations
        invariant
            0 <= i <= num_rotations,
            num_rotations < 4,
            n > 0,
            current_m.len() == n,
            forall|j: int| 0 <= j < current_m.len() ==> current_m[j].len() == n,
        decreases num_rotations - i
    {
        current_m = rotate_once(current_m);
        i = i + 1;
    }
    current_m
}
// </vc-code>

}
fn main() {}