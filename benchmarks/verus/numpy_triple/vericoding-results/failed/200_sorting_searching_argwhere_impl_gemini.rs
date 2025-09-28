// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proves that adding a larger element to the end of a sorted sequence preserves sortedness */
proof fn lemma_snoc_maintains_sorted(s: Seq<usize>, x: usize)
    requires
        (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]),
        (forall|i: int| 0 <= i < s.len() ==> s[i] < x),
    ensures
        (forall|i: int, j: int| 0 <= i < j < s.snoc(x).len() ==> s.snoc(x)[i] < s.snoc(x)[j]),
{
    let new_s = s.snoc(x);
    assert forall|i: int, j: int| 0 <= i < j < new_s.len() implies new_s[i] < new_s[j] by {
        if j < s.len() {
            // In this case, i and j are both indices into s.
            // new_s[i] is s[i] and new_s[j] is s[j].
            // The result holds because s is sorted.
        } else { // j == s.len()
            // In this case, i is an index into s, and new_s[j] is x.
            // new_s[i] is s[i].
            // The result holds because s[i] < x.
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices@.len() ==> 
            indices@[i] < a@.len() && a@[indices@[i] as int] != 0.0,

        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] != indices@[j],

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] < indices@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using correct lemmas and adding a helper lemma */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) && a@[k] != 0.0 ==> indices@.contains(k as usize),
            forall|j: int| 0 <= j < indices@.len() ==> 
                indices@[j] < i && a@[indices@[j] as int] != 0.0,
            forall|j1: int, j2: int| 0 <= j1 < j2 < indices@.len() ==> indices@[j1] < indices@[j2],
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            let old_indices = indices@;
            indices.push(i);

            proof {
                // Prove sortedness is maintained.
                assert forall|j: int| 0 <= j < old_indices.len() implies old_indices[j] < (i as usize) by {}
                lemma_snoc_maintains_sorted(old_indices, i as usize);

                // Prove 'contains' invariant is maintained.
                assert forall |k: int| 0 <= k < (i as int) + 1 && a@[k] != 0.0
                    implies indices@.contains(k as usize) by {
                    if k < i {
                        assert(old_indices.contains(k as usize));
                        vstd::seq::lemma_snoc_preserves_contains(old_indices, i as usize, k as usize);
                    } else { // k == i
                        vstd::seq::lemma_snoc_contains(old_indices, i as usize);
                    }
                }
            }
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}