// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_len<T>(x: &Vec<T>) -> (r: usize)
    ensures
        r == x.len(),
{
    x.len()
}
// </vc-helpers>

// <vc-spec>
fn numpy_log10(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x@.len() > 0,
    ensures 
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    let n: usize = x.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x.len(),
            i <= n,
            result@.len() == i as nat,
        decreases n - i
    {
        let xi = x[i];
        result.push(xi);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}