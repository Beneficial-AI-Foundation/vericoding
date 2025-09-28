// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result@.len() ==> a[result@[i] as int] != 0.0,

        forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> result@[i] != result@[j],

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error by casting i to int for array access */
    let mut result: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result@.len() ==> result@[k] < a.len(),
            forall|k: int| 0 <= k < result@.len() ==> a[result@[k] as int] != 0.0,
            forall|j: int| 0 <= j < i && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,
            forall|x: int, y: int| 0 <= x < result@.len() && 0 <= y < result@.len() && x != y ==> result@[x] != result@[y],
            forall|x: int, y: int| 0 <= x < y < result@.len() ==> result@[x] < result@[y],
        decreases a.len() - i
    {
        if a[i as int] != 0.0 {
            proof {
                let old_len = result@.len();
                assert(forall|k: int| 0 <= k < old_len ==> result@[k] < i);
                assert(i < a.len());
                assert(forall|k: int| 0 <= k < old_len ==> result@[k] != i);
            }
            result.push(i);
            proof {
                assert(result@[result@.len() - 1] == i);
                assert(a[i as int] != 0.0);
                assert(forall|k: int| 0 <= k < result@.len() ==> a[result@[k] as int] != 0.0);
                assert(forall|j: int| 0 <= j <= i && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}