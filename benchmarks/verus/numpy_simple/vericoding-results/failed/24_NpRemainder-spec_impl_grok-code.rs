// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
/* code modified by LLM (iteration 2): implement remainder using loop with proper invariants */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i as int,
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i
    {
        result.push(a[i] % b[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}