// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): create vec of len1 */
fn vec_of_len1(x: usize) -> (result: Vec<usize>)
    ensures
        result.len() == 1,
        result[0] == x
{
    let mut v: Vec<usize> = Vec::new();
    v.push(x);
    v
}

/* helper modified by LLM (iteration 3): create vec of len2 */
fn vec_of_len2(a: usize, b: usize) -> (result: Vec<usize>)
    ensures
        result.len() == 2,
        result[0] == a,
        result[1] == b
{
    let mut v: Vec<usize> = Vec::new();
    v.push(a);
    v.push(b);
    v
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
{
    /* code modified by LLM (iteration 3): shape_arrays cases */
    match a {
        Arrays::ArrayOne(arr) => {
            let mut result: Vec<usize> = Vec::new();
            result.push(arr.len());
            result
        },
        Arrays::ArrayTwo(arr) => {
            let mut result: Vec<usize> = Vec::new();
            result.push(arr.len());
            let second = if arr.len() > 0 { arr[0].len() } else { 0 };
            result.push(second);
            result
        },
        Arrays::ArrayThree(arr) => {
            let mut result: Vec<usize> = Vec::new();
            result.push(arr.len());
            let second = if arr.len() > 0 { arr[0].len() } else { 0 };
            result.push(second);
            let third = if arr.len() > 0 && arr[0].len() > 0 { arr[0][0].len() } else { 0 };
            result.push(third);
            result
        },
    }
}

{
    /* code modified by LLM (iteration 3): shape_matrix returns dims */
    let mut result: Vec<usize> = Vec::new();
    result.push(a.m);
    result.push(a.n);
    result
}
// </vc-code>


}
fn main() {}