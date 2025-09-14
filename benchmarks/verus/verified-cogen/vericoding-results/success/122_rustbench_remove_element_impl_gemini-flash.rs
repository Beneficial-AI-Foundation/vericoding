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
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < pos
        invariant
            0 <= i <= pos,
            result.len() == i as int,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases pos - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    let mut j = pos + 1;
    while j < a.len()
        invariant
            pos + 1 <= j <= a.len(),
            result.len() == i as int + (j - (pos + 1)) as int,
            forall|k: int| 0 <= k < pos ==> result[k] == a[k],
            forall|k: int| pos <= k < result.len() ==> result[k] == a[k + 1],
        decreases a.len() - j
    {
        result.push(a[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}