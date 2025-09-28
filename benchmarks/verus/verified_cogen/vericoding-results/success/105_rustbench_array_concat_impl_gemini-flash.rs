// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): remove unused helper */
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): add decreases clauses to loops */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == a@[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }

    let mut k = 0;
    while k < b.len()
        invariant
            0 <= k && k <= b.len(),
            result.len() == a.len() + k,
            forall|j: int| 0 <= j && j < a.len() ==> result@[j] == a@[j],
            forall|j: int| 0 <= j && j < k ==> result@[a.len() + j] == b@[j],
        decreases b.len() - k
    {
        result.push(b[k]);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}