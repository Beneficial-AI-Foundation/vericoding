// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): change to use usize for indices and lengths */
proof fn index_in_bounds(i: usize, j: usize, n1: usize, n2: usize, result_len: usize)
    requires i < n1 && j < n2 && result_len == n1 + n2 - 1,
    ensures i+j < result_len
{
    assert(i+j <= n1-1 + n2-1);
    assert(n1-1+n2-1 == n1+n2-2);
    assert(n1+n2-2 < n1+n2-1);
}
// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1.len() > 0 && c2.len() > 0,
    ensures 
        result.len() == c1.len() + c2.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1.len() && 
                    0 <= k < c2.len() && 
                    j + k == i && 
                    c1[j] != 0.0 && 
                    c2[k] != 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use usize for lengths and indices, and update proof call */
{
    let n1: usize = c1.len();
    let n2: usize = c2.len();
    let result_len: usize = n1 + n2 - 1;

    let mut result = Vec::new();
    for _ in 0..result_len {
        result.push(0.0);
    }

    for i in 0..n1 {
        for j in 0..n2 {
            let index = i + j;
            proof {
                index_in_bounds(i, j, n1, n2, result_len);
            }
            let old_value = result[index];
            let product = c1[i] * c2[j];
            result[index] = old_value + product;
        }
    }
    result
}
// </vc-code>

}
fn main() {}