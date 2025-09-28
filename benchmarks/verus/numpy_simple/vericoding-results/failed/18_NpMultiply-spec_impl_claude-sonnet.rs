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
{
    /* code modified by LLM (iteration 5): fixed bounds check in invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == a@[j] as int * b@[j] as int,
            a.len() == b.len(),
        decreases a.len() - i
    {
        let product = #[verifier::truncate] ((a[i] as i32 * b[i] as i32) as i8);
        result.push(product);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}