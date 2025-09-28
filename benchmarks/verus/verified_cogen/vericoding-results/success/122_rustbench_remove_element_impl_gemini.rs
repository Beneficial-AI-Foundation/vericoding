// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    requires
        0 <= pos < a.len(),
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): corrected invariants for the second loop */
{
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < pos
        invariant
            0 <= i <= pos,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases pos - i
    {
        result.push(a[i]);
        i = i + 1;
    }

    i = pos + 1;
    while i < a.len()
        invariant
            pos + 1 <= i <= a.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < pos ==> result[j] == a[j],
            forall|j: int| pos <= j < i - 1 ==> result[j] == a[j + 1],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}