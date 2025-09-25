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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}