// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diag(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures 
        result.len() == v.len(),
        forall|i: int| 0 <= i < v@.len() ==> result@[i].len() == v@.len(),
        /* Elements on the main diagonal are from v */
        forall|i: int| 0 <= i < v@.len() ==> result@[i][i] == v@[i],
        /* All off-diagonal elements are zero */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
        /* Diagonal matrix property - non-zero elements only on diagonal */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && result@[i][j] != 0.0f32 ==> i == j,
        /* The resulting matrix is symmetric */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> result@[i][j] == result@[j][i],
        /* Each row has exactly one non-zero element at position i (unless v[i] = 0) */
        forall|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> {
            result@[i][i] != 0.0f32 && 
            forall|j: int| 0 <= j < v@.len() && j != i ==> result@[i][j] == 0.0f32
        },
        /* Each column has exactly one non-zero element at position j (unless v[j] = 0) */
        forall|j: int| 0 <= j < v@.len() && v@[j] != 0.0f32 ==> {
            result@[j][j] != 0.0f32 && 
            forall|i: int| 0 <= i < v@.len() && i != j ==> result@[i][j] == 0.0f32
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed nat to usize for executable code */
{
    let n = v.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i as int <= n as int,
            result.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> {
                result@[k].len() == n as int &&
                result@[k][k] == v@[k] &&
                forall|j: int| 0 <= j < n as int && j != k ==> result@[k][j] == 0.0f32
            },
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j as int <= n as int,
                row.len() == j as int,
                forall|k: int| 0 <= k < j as int && k != i as int ==> row@[k] == 0.0f32,
                j as int > i as int || row@(i as int) == 0.0f32,
            decreases n - j
        {
            if j == i {
                row.push(v[j]);
            } else {
                row.push(0.0f32);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}