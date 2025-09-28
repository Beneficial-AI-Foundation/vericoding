// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added (as int) casts for all a[index] accesses to fix type mismatches from usize to int */
fn find_min(indices: &[usize], start: usize, a: &[i8]) -> (result: usize)
    requires
        start < indices.len(),
        indices.len() == a.len(),
        forall|j: int| 0 <= j < indices.len() ==> 0 <= indices[j] < a.len(),
    ensures
        start <= result < indices.len(),
        forall|j: int| start <= j < indices.len() ==> a[(indices[result] as int)] <= a[(indices[j] as int)],
{
    let mut result = start;
    let mut j = start + 1;
    while j < indices.len()
        invariant
            start <= result < j <= indices.len(),
            forall|k: int| start <= k < j ==> a[(indices[result] as int)] <= a[(indices[k] as int)],
        decreases indices.len() - j,
    {
        if a[(indices[j] as int)] < a[(indices[result] as int)] {
            result = j;
        }
        j += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] a@[result@[i] as int] <= #[trigger] a@[result@[j] as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added (as int) casts for a[index] in invariants to fix type mismatches */
    let len = a.len();
    let mut indices: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            indices.len() == i,
            i <= len,
    {
        indices.push(i);
        i += 1;
    }
    let mut i = 0;
    while i < len - 1
        invariant
            indices.len() == len,
            forall|k: int| 0 <= k < i ==> forall|m: int| i <= m < len ==> a[(indices[k] as int)] <= a[(indices[m] as int)],
            forall|k: int| 0 <= k < len ==> 0 <= indices[k] < a.len(),
            i <= len - 1,
        decreases len - i,
    {
        let min_idx = find_min(&indices, i, &a.as_slice());
        let temp = indices[i];
        indices[i] = indices[min_idx];
        indices[min_idx] = temp;
        i += 1;
    }
    indices
}
// </vc-code>


}
fn main() {}