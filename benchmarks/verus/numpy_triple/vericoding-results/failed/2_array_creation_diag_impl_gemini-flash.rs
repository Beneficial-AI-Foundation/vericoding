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
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing semicolon from forall clause. */
    let n = v.len();
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            result.spec_len() == i as nat,
            forall|idx: int| 0 <= idx < i ==> result@[idx].len() == n,
            forall|idx: int, jdx: int| 0 <= idx < i && 0 <= jdx < n ==> {
                if idx == jdx {
                    result@[idx][jdx] == v@[idx]
                } else {
                    result@[idx][jdx] == 0.0f32
                }
            },
            0 <= i <= n,
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < n
            invariant
                row.len() == j,
                row.spec_len() == j as nat,
                forall|idx: int| 0 <= idx < j ==> {
                    if idx == i {
                        row@[idx] == v@[i]
                    } else {
                        row@[idx] == 0.0f32
                    }
                },
                0 <= j <= n,
                0 <= i < n,
        {
            if i == j {
                row.push(v@[i]);
            } else {
                row.push(0.0f32);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    
    proof {
        assert forall|idx: int| 0 <= idx < n implies result@[idx].len() == n by {
            // Each row is constructed to have length `n`
        };
        assert forall|idx: int| 0 <= idx < n implies result@[idx][idx] == v@[idx] by {
            // The diagonal elements are set to v[i] directly during construction
        };
        assert forall|idx: int, jdx: int| 0 <= idx < n && 0 <= jdx < n && idx != jdx implies result@[idx][jdx] == 0.0f32 by {
            // Off-diagonal elements are explicitly set to 0.0f32
        };

        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n && result@[i][j] != 0.0f32 implies i == j by {
            if i != j {
                // If i != j, then result@[i][j] is constructed as 0.0f32, which contradicts result@[i][j] != 0.0f32.
                // So, the premise i != j must be false, meaning i == j.
            }
        };

        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies result@[i][j] == result@[j][i] by {
            if i == j {
                // result[i][i] == v[i]
            } else {
                // result[i][j] == 0.0f32 && result[j][i] == 0.0f32
            }
        };

        assert forall|i: int| 0 <= i < n && v@[i] != 0.0f32 implies {
            result@[i][i] != 0.0f32 && 
            (forall|j: int| 0 <= j < n && j != i implies result@[i][j] == 0.0f32)
        } by {
            // This follows directly from construction
        };

         assert forall|j: int| 0 <= j < n && v@[j] != 0.0f32 implies {
            result@[j][j] != 0.0f32 && 
            (forall|i: int| 0 <= i < n && i != j implies result@[i][j] == 0.0f32)
        } by {
            // This also follows directly from construction (and symmetry)
        };

    }
    result
}
// </vc-code>


}
fn main() {}