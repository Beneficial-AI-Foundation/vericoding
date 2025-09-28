// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct a Vec [x] and ensure contents */
fn make_singleton(x: usize) -> (result: Vec<usize>)
    ensures
        result.len() == 1,
        result[0] == x,
{
    let mut v: Vec<usize> = Vec::new();
    v.push(x);
    v
}

/* helper modified by LLM (iteration 5): construct a Vec [a, b] and ensure contents */
fn make_pair(a: usize, b: usize) -> (result: Vec<usize>)
    ensures
        result.len() == 2,
        result[0] == a,
        result[1] == b,
{
    let mut v: Vec<usize> = Vec::new();
    v.push(a);
    v.push(b);
    v
}

/* helper modified by LLM (iteration 5): construct a Vec [a, b, c] and ensure contents */
fn make_triple(a: usize, b: usize, c: usize) -> (result: Vec<usize>)
    ensures
        result.len() == 3,
        result[0] == a,
        result[1] == b,
        result[2] == c,
{
    let mut v: Vec<usize> = Vec::new();
    v.push(a);
    v.push(b);
    v.push(c);
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
    /* code modified by LLM (iteration 5): compute shape vectors for Arrays and Matrix using helpers */
    match a {
        Arrays::ArrayOne(arr) => {
            make_singleton(arr.len())
        }
        Arrays::ArrayTwo(arr) => {
            let inner_len: usize = if arr.len() > 0 { arr[0].len() } else { 0 };
            make_pair(arr.len(), inner_len)
        }
        Arrays::ArrayThree(arr) => {
            let d1: usize = if arr.len() > 0 { arr[0].len() } else { 0 };
            let d2: usize = if arr.len() > 0 && d1 > 0 { arr[0][0].len() } else { 0 };
            make_triple(arr.len(), d1, d2)
        }
    }
}
{
    /* code modified by LLM (iteration 5): return [m, n] for matrix shape via helper */
    make_pair(a.m, a.n)
}
// </vc-code>


}
fn main() {}