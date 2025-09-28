// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use named return type to fix compilation error */
fn compute_result_length(fname_len: u8, skiprows: u8) -> (result: usize)
    requires
        fname_len as nat > 0,
        skiprows as nat >= 0,
    ensures
        result >= 0,
{
    let n = fname_len as usize;
    let skip = skiprows as usize;
    if n > skip {
        n - skip
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn loadtxt(fname_len: u8, skiprows: u8) -> (result: Vec<f64>)
    requires 
        fname_len as nat > 0,
        skiprows as nat >= 0,
    ensures
        result@.len() >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): create vector by pushing elements in a loop to avoid unsupported vec! macro */
    let len = compute_result_length(fname_len, skiprows);
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result@.len() == i,
        decreases len - i,
    {
        result.push(0.0);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}