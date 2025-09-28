// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Convert to int for addition to avoid overflow, then cast back. This may fail on the cast. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == a@[j] as int + b@[j] as int,
        decreases a.len() - i
    {
        let sum = a[i] as int + b[i] as int;
        assert(i8::MIN as int <= sum <= i8::MAX as int) by {
            // The ensures clause of `add` guarantees that there exists a `result` vector
            // where `result[i] as int == a[i] as int + b[i] as int`. 
            // This implies the sum must be representable as an i8.
            // However, we cannot directly use the ensures clause of the function we are implementing.
            // This proof is thus left empty, and is expected to fail.
            // By using this structure, we pinpoint the exact missing assumption.
        }
        let val = sum as i8;
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}