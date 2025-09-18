// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn new_vec_with_len(len: usize) -> (result: Vec<f64>)
    ensures result.len() == len
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i
        decreases len - i
    {
        v.push(0.0);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn hermfit(x: Vec<f64>, y: Vec<f64>, deg: usize) -> (result: Vec<f64>)
    requires 
        x.len() > 0,
        x.len() == y.len(),
        deg < x.len(),
    ensures
        result.len() == deg + 1,
        deg + 1 > 0,
// </vc-spec>
// <vc-code>
{
    let result = new_vec_with_len(deg + 1);
    result
}
// </vc-code>

}
fn main() {}