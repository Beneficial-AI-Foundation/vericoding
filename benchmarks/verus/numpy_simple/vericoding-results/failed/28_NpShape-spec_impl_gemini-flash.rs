// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a helper `get_dim_safe` to safely retrieve vector dimensions, returning 0 for empty vectors. */
spec fn get_dim_safe<T>(v: &Vec<T>) -> usize {
    if v.len() > 0 {
        v.len()
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
struct Matrix<T> {
    m: usize,
    n: usize,
    data: Vec<Vec<T>>,
}

impl<T> Matrix<T> {
    spec fn size(&self) -> nat {
        (self.m as nat) * (self.n as nat)
    }
}

enum Arrays {
    ArrayOne(Vec<f32>),
    ArrayTwo(Vec<Vec<f32>>),
    ArrayThree(Vec<Vec<Vec<f32>>>),
}

spec fn arrays_ndim(a: &Arrays) -> nat {
    match a {
        Arrays::ArrayOne(_) => 1nat,
        Arrays::ArrayTwo(_) => 2nat,
        Arrays::ArrayThree(_) => 3nat,
    }
}

fn shape_arrays(a: &Arrays) -> (result: Vec<usize>)
    ensures
        result.len() == arrays_ndim(a),
        match a {
            Arrays::ArrayOne(arr) => result.len() == 1 && result[0] == arr.len(),
            Arrays::ArrayTwo(arr) => result.len() == 2 && result[0] == arr.len() && 
                result[1] == (if arr.len() > 0 { arr[0].len() } else { 0 }),
            Arrays::ArrayThree(arr) => result.len() == 3 && result[0] == arr.len() && 
                result[1] == (if arr.len() > 0 { arr[0].len() } else { 0 }) &&
                result[2] == (if arr.len() > 0 && arr[0].len() > 0 { arr[0][0].len() } else { 0 })
        }
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn shape_matrix(a: &Matrix<f32>) -> (result: Vec<usize>)
    ensures
        result.len() == 2,
        result[0] == a.m,
        result[1] == a.n
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented `shape_arrays` to correctly return the shape for 1D, 2D, and 3D arrays by handling different `Arrays` enum variants. */
{
    match a {
        Arrays::ArrayOne(arr) => {
            let mut result = Vec::new();
            result.push(arr.len());
            result
        },
        Arrays::ArrayTwo(arr) => {
            let mut result = Vec::new();
            result.push(arr.len());
            let inner_len = if arr.len() > 0 { arr[0].len() } else { 0 };
            result.push(inner_len);
            result
        },
        Arrays::ArrayThree(arr) => {
            let mut result = Vec::new();
            result.push(arr.len());
            let dim1 = if arr.len() > 0 { arr[0].len() } else { 0 };
            result.push(dim1);
            let dim2 = if arr.len() > 0 && arr[0].len() > 0 { arr[0][0].len() } else { 0 };
            result.push(dim2);
            result
        }
    }
}
// </vc-code>


}
fn main() {}