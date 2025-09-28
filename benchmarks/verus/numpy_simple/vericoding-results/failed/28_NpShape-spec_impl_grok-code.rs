// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    match a {
        Arrays::ArrayOne(arr) => {
            vec![arr.len()]
        },
        Arrays::ArrayTwo(arr) => {
            let len1 = if arr.is_empty() {
                0
            } else {
                arr[0].len()
            };
            vec![arr.len(), len1]
        },
        Arrays::ArrayThree(arr) => {
            let len1 = if arr.is_empty() {
                0
            } else {
                arr[0].len()
            };
            let len2 = if arr.is_empty() || arr[0].is_empty() {
                0
            } else {
                arr[0][0].len()
            };
            vec![arr.len(), len1, len2]
        }
    }
}

fn shape_matrix(a: &Matrix<f32>) -> (result: Vec<usize>)
    ensures
        result.len() == 2,
        result[0] == a.m,
        result[1] == a.n
{
    vec![a.m, a.n]
}
// </vc-code>


}
fn main() {}