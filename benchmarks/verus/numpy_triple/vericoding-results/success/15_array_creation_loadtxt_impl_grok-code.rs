// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): fixed unsupported i32 to f64 cast by using conditional f64 literals based on i */
    let fl = fname_len as usize;
    let sr = skiprows as usize;
    let len = if fl > sr { fl - sr } else { 0 };
    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant
            result@.len() == i,
            i <= len,
        decreases len - i,
    {
        let val = if i % 2 == 0 { 0.0 } else { 0.5 };
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}