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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0u8;
    
    while i < fname_len
        invariant
            i <= fname_len,
            result@.len() >= 0,
        decreases fname_len - i
    {
        if i >= skiprows {
            result.push(0.0);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}