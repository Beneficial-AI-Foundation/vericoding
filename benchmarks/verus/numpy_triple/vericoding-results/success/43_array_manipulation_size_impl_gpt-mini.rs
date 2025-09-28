// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): pure wrapper returning vector length */
fn vec_len<T>(v: &Vec<T>) -> (len: usize)
    ensures
        len == v.len(),
{
    v.len()
}
// </vc-helpers>

// <vc-spec>
fn size(a: &Vec<f64>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return vector length using helper */
    let result: usize = vec_len(a);
    result
}
// </vc-code>

}
fn main() {}