// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove usize cast nonneg */
fn lemma_usize_nonneg(n: usize)
    ensures
        (n as int) >= 0,
{
    proof {
        assert(n as int >= 0);
    }
}
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
    /* code modified by LLM (iteration 5): iterate a, collect indices of nonzeros with correct loop invariants and proofs */
    let mut indices = Vec::<usize>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall|k: int| 0 <= k < (indices@).len() as int ==> ((indices@)[k] < a.len() && (a@)[(indices@)[k] as int] != 0.0f32),
            forall|j: int| 0 <= j < i as int ==> ((a@)[j] != 0.0f32 <==> exists|k: int| 0 <= k < (indices@).len() as int && (indices@)[k] == j),
            forall|i1: int, i2: int| 0 <= i1 < i2 < (indices@).len() as int ==> (indices@)[i1] < (indices@)[i2],
            (indices@).len() as int <= i as int,
        decreases
            a.len() - i
    {
        let idx: usize = i;
        let v: f32 = a[idx];
        let prev_len: int = (indices@).len() as int;
        i += 1;
        if v != 0.0f32 {
            indices.push(idx);
        }
        proof {
            // bounds and relation of runtime value to spec view
            assert(idx < a.len());
            assert((a@)[idx as int] == v);
            if v != 0.0f32 {
                assert((indices@).len() as int == prev_len + 1);
                assert((indices@)[prev_len] == idx);
                assert((a@)[idx as int] != 0.0f32);
            }

            assert(forall|j: int| 0 <= j < i as int ==> ((a@)[j] != 0.0f32 <==> exists|k: int| 0 <= k < (indices@).len() as int && (indices@)[k] == j)));
            assert(forall|i1: int, i2: int| 0 <= i1 < i2 < (indices@).len() as int ==> ((indices@)[i1] < (indices@)[i2])));
            assert((indices@).len() as int <= i as int);
        }
    }
    indices
}
// </vc-code>

}
fn main() {}