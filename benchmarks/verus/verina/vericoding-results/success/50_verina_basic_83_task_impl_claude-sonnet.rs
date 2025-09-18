// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn concat(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] == b[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed initial invariant and length bounds */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            result.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k < j ==> result[k + a.len()] == b[k],
        decreases b.len() - j
    {
        result.push(b[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}