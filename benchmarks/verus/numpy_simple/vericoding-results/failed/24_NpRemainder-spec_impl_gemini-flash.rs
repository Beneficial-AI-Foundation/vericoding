// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
fn create_remainder_vec(length: usize) -> (result: Vec<i8>)
    requires
        length >= 0,
    ensures
        result.len() == length
{
    // Create a vector of the given length, initialized with zeros.
    let mut vec: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < length
        invariant 
            vec.len() == i,
            0 <= i,
            i <= length,
            // All elements in vec are 0 so far
            forall|j: int| 0 <= j < i ==> vec[j] == 0,
        decreases (length - i)
    {
        vec.push(0);
        i = i + 1;
    }
    vec
}
// </vc-helpers>

// <vc-spec>
fn remainder(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting for vector access to use `i` directly as `usize`. */
{
    let length = a.len();
    let mut result: Vec<i8> = Vec::new();

    let mut i: usize = 0;
    while i < length
        invariant
            result.len() == i,
            0 <= i,
            i <= length,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
        decreases length - i
    {
        proof {
            assert(0 <= i && i < a.len());
            assert(0 <= i && i < b.len());
            assert(b@[i as int] != 0);
        }
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}