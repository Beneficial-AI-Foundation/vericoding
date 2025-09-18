// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_tofile(arr: Vec<f32>, filename: String) -> (result: ())
    requires true,
    ensures result == ()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to prove loop termination */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
        decreases arr.len() - i
    {
        i = i + 1;
    }
    ()
}
// </vc-code>

}
fn main() {}