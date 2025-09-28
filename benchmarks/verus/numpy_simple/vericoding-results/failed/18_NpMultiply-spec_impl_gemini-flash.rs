// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == a[i] as int * b[i] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Correcting the use of `get_spec` to `@`. */
{
    let len = a.len();
    let mut result_vec = Vec::with_capacity(len as usize);
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i as int,
            i as int <= len as int,
            result_vec.len() == i,
            result_vec.capacity() == len,
            forall|j: int| 0 <= j < i as int ==> result_vec@[j] as int == a@[j] as int * b@[j] as int,
        decreases len - i
    {
        result_vec.push(a[i] * b[i]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}