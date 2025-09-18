// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_result_indices_valid(a: &Vec<f64>, result: &Vec<usize>, i: usize)
    requires
        i < result.len(),
        forall|idx: int| 0 <= idx < result.len() ==> result[idx as int] < a.len(),
    ensures
        result[i as int] < a.len(),
{
}

proof fn lemma_monotonic_ordering(result: &Vec<usize>, i: usize, j: usize)
    requires
        i < j,
        j < result.len(),
        forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
    ensures
        result[i as int] < result[j as int],
{
}

/* helper modified by LLM (iteration 5): added proof assertion to help with loop invariant maintenance */
proof fn lemma_push_preserves_invariants(old_result: &Vec<usize>, new_idx: usize, old_i: usize)
    requires
        forall|idx: int| 0 <= idx < old_result.len() ==> old_result[idx] < old_i,
        forall|x: int, y: int| 0 <= x < y < old_result.len() ==> old_result[x] < old_result[y],
        old_result.len() == 0 || old_result[old_result.len() as int - 1] < new_idx,
    ensures
        true
{
}
// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result.len() ==> a[result[i] as int] != 0.0,

        forall|j: int| 0 <= j < a.len() && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,

        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof blocks to maintain loop invariants */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|idx: int| 0 <= idx < result.len() ==> result[idx] < a.len(),
            forall|idx: int| 0 <= idx < result.len() ==> a[result[idx] as int] != 0.0,
            forall|j: int| 0 <= j < i && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
            forall|x: int, y: int| 0 <= x < result.len() && 0 <= y < result.len() && x != y ==> result[x] != result[y],
            forall|idx: int| 0 <= idx < result.len() ==> result[idx] < i,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            proof {
                assert(result.len() == 0 || result[result.len() as int - 1] < i);
                assert(i < a.len());
            }
            result.push(i);
            proof {
                assert(forall|idx: int| 0 <= idx < result.len() - 1 ==> result[idx] < i);
                assert(result[result.len() as int - 1] == i);
                assert(forall|idx: int| 0 <= idx < result.len() ==> a[result[idx] as int] != 0.0);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}