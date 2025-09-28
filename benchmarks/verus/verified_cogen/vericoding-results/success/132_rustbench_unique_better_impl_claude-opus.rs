// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added trigger annotations to fix quantifier trigger inference */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int| #![trigger result[k], result[l]] 0 <= k && k < l && l < result.len() ==> result[k] < result[l],
            result.len() == 0 || (i > 0 && a[i - 1] == result[result.len() - 1]),
            forall|k: int| #![trigger result[k]] 0 <= k && k < result.len() ==> exists|m: int| #![trigger a[m]] 0 <= m && m < i && a[m] == result[k],
        decreases a.len() - i
    {
        if i == 0 || a[i] != a[i - 1] {
            result.push(a[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}