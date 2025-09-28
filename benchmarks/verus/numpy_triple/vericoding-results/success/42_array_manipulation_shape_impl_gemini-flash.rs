// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): moved shape helper function outside of vc-helpers to prevent duplicate definition */
// </vc-helpers>

// <vc-spec>
fn shape<T>(a: &Vec<T>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): returns the length of the input vector as its shape */
    a.len()
}
// </vc-code>

}
fn main() {}