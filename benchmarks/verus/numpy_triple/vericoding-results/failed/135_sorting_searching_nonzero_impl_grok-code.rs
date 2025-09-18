// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): none required */
// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced Vec indexing with @ for int indexes in invariants and proofs */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> (result@[k] as int < i as int && a@[result@[k] as int] != 0.0f32),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result@[k1] < result@[k2],
            forall|j: int| 0 <= j < i ==> (a@[j] != 0.0f32 <==> exists|k: int| 0 <= k < result.len() && result@[k] == j),
        decreases a.len() - i,
    {
        if a@[i as int] != 0.0f32 {
            result.push(i);
        }
        i += 1;
    }
    proof {
        // prove first postcondition
        assert(forall|i: int| 0 <= i < result.len() ==> (result@[i] as int < a.len() as int && a@[result@[i] as int] != 0.0f32)) by ({
            forall|i: int| 0 <= i < result.len()
                ensures result@[i] as int < a.len() as int && a@[result@[i] as int] != 0.0f32 {
                assert(result@[i] as int < i as int); // holds from invariant
                assert(i as int <= a.len() as int); // true since usize to int preserves order and loop condition i <= a.len() at end
            }
        });
        // prove second postcondition
        assert(forall|j: int| 0 <= j < a.len() ==> (a@[j] != 0.0f32 <==> exists|k: int| 0 <= k < result.len() && result@[k] == j));
        // the invariant already covers this directly since i == a.len()
        // prove monotonic
        assert(forall|i1: int, i2: int| 0 <= i1 < i2 < result.len() ==> result@[i1] < result@[i2]); // directly from invariant
        // prove uniqueness
        assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]) by ({
            forall|i: int, j: int| i < j && 0 <= i < j < result.len() && result@[i] == result@[j] {
                assert(result@[i] < result@[j]); // from monotonic
                assert(result@[j] <= result@[j]); // trivial
                assert(result@[i] < result@[i]); // contradiction from ==
            }
        });
    }
    result
}
// </vc-code>

}
fn main() {}