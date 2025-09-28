// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
/* Matrix type represented as a 2D vector */
type Matrix<T> = Vec<Vec<T>>;

fn diagonal(arr: Matrix<i8>, k: i8) -> (result: Vec<i8>)
    requires 
        arr.len() > 0,
        arr.len() == arr[0].len(), /* square matrix */
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr.len(),
        -(arr.len() as i8) < k && k < (arr.len() as i8),
    ensures
        if k > 0 {
            result.len() == arr.len() - (k as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i][i + (k as usize)]
        } else {
            result.len() == arr.len() + ((-k) as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i + ((-k) as usize)][i]
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Resolved compilation errors. Replaced `view_mut()@[j]` with `view()@[j]` for `result` and corrected `view()` method calls for `arr` to access inner `Vec<i8>` elements correctly. */
{
    let n = arr.len();
    let mut result: Vec<i8> = Vec::new();

    if k >= 0 {
        let k_abs = k as usize;
        let len = n - k_abs; // Length of the diagonal
        let mut i = 0;

        while i < len
            invariant
                0 <= i && i <= len,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> 
                    ({
                        let row_idx_j = j as usize;
                        let col_idx_j = j as usize + k_abs;
                        row_idx_j < n && col_idx_j < n 
                    }),
                forall|j: int| 0 <= j < i ==> result.view()@[j] == arr.view()@[j as usize].view()@[j as usize + k_abs],
            decreases len - i
        {
            result.push(arr.view()@[i as usize].view()@[i as usize + k_abs]);
            i = i + 1;
        }
    } else {
        let k_abs = (-k) as usize;
        let len = n - k_abs; // Length of the diagonal
        let mut i = 0;

        while i < len
            invariant
                0 <= i && i <= len,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> 
                    ({
                        let row_idx_j = j as usize + k_abs;
                        let col_idx_j = j as usize;
                        row_idx_j < n && col_idx_j < n 
                    }),
                forall|j: int| 0 <= j < i ==> result.view()@[j] == arr.view()@[j as usize + k_abs].view()@[j as usize],
            decreases len - i
        {
            result.push(arr.view()@[i as usize + k_abs].view()@[i as usize]);
            i = i + 1;
        }
    }
    result
}
// </vc-code>


}
fn main() {}