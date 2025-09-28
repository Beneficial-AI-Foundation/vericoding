// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
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
    /* code modified by LLM (iteration 3): fixed length calculation for diagonal extraction */
    let n = arr.len();
    let mut result = Vec::new();
    if k > 0 {
        let m = k as usize;
        for i in 0..(n - m)
        invariant
            result.len() == (i as nat),
            forall|j: int| 0 <= j < (i as int) ==> result[j] == arr[j][j + m],
            forall|j: int| 0 <= j < (i as int) ==> j + m < n
        {
            result.push(arr[i][i + m]);
        }
    } else {
        let offset = ((-k) as usize);
        for i in 0..(n - offset)
        invariant
            result.len() == (i as nat),
            forall|j: int| 0 <= j < (i as int) ==> result[j] == arr[j + offset][j],
            forall|j: int| 0 <= j < (i as int) ==> j + offset < n
        {
            result.push(arr[i + offset][i]);
        }
    }
    result
}
// </vc-code>


}
fn main() {}