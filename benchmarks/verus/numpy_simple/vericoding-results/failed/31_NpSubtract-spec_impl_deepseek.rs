// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed index types and simplified sequence implementation */
fn vec_subtract_spec(a: Seq<i8>, b: Seq<i8>) -> (result: Seq<i8>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] - b[i],
{
    let mut result = Seq::empty();
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] - b[j],
        decreases a.len() - i,
    {
        result = result.insert(i, a[i] - b[i]);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn subtract(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[i] - b@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed usize vs int comparison and vector indexing */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let n = a.len();
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] - b@[j],
        decreases n - i,
    {
        result.push(a[i as usize] - b[i as usize]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}