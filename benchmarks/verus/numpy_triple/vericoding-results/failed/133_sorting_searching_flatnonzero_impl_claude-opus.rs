// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed type errors in array indexing */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < result.len() ==> a[result[j] as int] != 0.0,
            forall|j: int| 0 <= j < i && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,
            forall|p: int, q: int| 0 <= p < result.len() && 0 <= q < result.len() && p != q ==> result[p] != result[q],
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] < result[q],
            forall|j: int| 0 <= j < result.len() ==> result[j] < i
        decreases a.len() - i
    {
        if a[i as int] != 0.0 {
            let old_result = result;
            result.push(i);
            assert(result[result.len() - 1] == i);
            assert(forall|j: int| 0 <= j < old_result.len() ==> old_result[j] == result[j]);
            assert(forall|j: int| 0 <= j < old_result.len() ==> result[j] < i);
            assert(a[i as int] != 0.0);
            assert(a[result[result.len() - 1] as int] != 0.0);
            assert(forall|j: int| 0 <= j < old_result.len() ==> a[result[j] as int] != 0.0);
            assert(exists|k: int| 0 <= k < result.len() && result[k] == i);
        }
        assert(a[i as int] == 0.0 || exists|k: int| 0 <= k < result.len() && result[k] == i);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}