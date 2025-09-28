// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch in requires clause */
fn matrix_get(arr: &Matrix<i8>, row: usize, col: usize) -> i8
    requires
        arr.len() > 0,
        0 <= row < arr.len(),
        0 <= col < arr[row as int].len(),
{
    arr[row][col]
}

fn compute_diagonal_length(n: usize, k: i8) -> usize
    requires
        n > 0,
        -(n as i8) < k && k < (n as i8),
{
    if k > 0 {
        n - (k as usize)
    } else {
        n + ((-k) as usize)
    }
}
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
    /* code modified by LLM (iteration 5): added decreases clauses to both while loops */
    let n = arr.len();
    let mut result = Vec::new();
    
    if k > 0 {
        let len = n - (k as usize);
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                len == n - (k as usize),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j as int] == arr[j as int][j + (k as int)],
            decreases len - i
        {
            result.push(arr[i][i + (k as usize)]);
            i += 1;
        }
    } else {
        let offset = (-k) as usize;
        let len = n + offset;
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                offset == (-k) as usize,
                len == n + offset,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j as int] == arr[j + ((-k) as int)][j as int],
            decreases len - i
        {
            result.push(arr[i + offset][i]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}