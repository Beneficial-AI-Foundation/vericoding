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
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loops */
    let n = arr.len();
    let mut result = Vec::new();
    
    if k > 0 {
        let k_usize = k as usize;
        let mut i: usize = 0;
        while i < n - k_usize
            invariant
                0 <= i <= n - k_usize,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == arr[j][j + k_usize],
            decreases n - k_usize - i
        {
            result.push(arr[i][i + k_usize]);
            i = i + 1;
        }
    } else {
        let neg_k_usize = (-k) as usize;
        let mut i: usize = 0;
        while i < n - neg_k_usize
            invariant
                0 <= i <= n - neg_k_usize,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == arr[j + neg_k_usize][j],
            decreases n - neg_k_usize - i
        {
            result.push(arr[i + neg_k_usize][i]);
            i = i + 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}