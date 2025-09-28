// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn equal(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (a@[i] == b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed array access bounds checking */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j] == b@[j]),
        decreases a.len() - i
    {
        let eq = a[i] == b[i];
        result.push(eq);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}