// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed helper function since Vec::len() can be used directly */
// </vc-helpers>

// <vc-spec>
fn size(a: &Vec<f64>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Directly return a.len() without helper */
{
    a.len()
}
// </vc-code>

}
fn main() {}