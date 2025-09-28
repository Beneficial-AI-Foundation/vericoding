// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn r_(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        forall|j: int| 0 <= j < b.len() ==> result[a.len() + j] == b[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses to both while loops to ensure termination */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    let mut j = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            result.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k < j ==> result[a.len() + k] == b[k],
        decreases b.len() - j
    {
        result.push(b[j]);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}