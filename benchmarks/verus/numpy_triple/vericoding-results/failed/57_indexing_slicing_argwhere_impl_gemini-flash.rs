// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices@.len() ==> (#[trigger] indices@[i] as int) < a@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> a@[indices@[i] as int] != 0.0,
        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == i,
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices@[i] != indices@[j],
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && (indices@[i] as int) < (indices@[j] as int) ==> i < j,
        (indices@.len() == 0) == (forall|i: int| 0 <= i < a@.len() ==> a@[i] == 0.0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected error in the invariant for the while loop and provided more explicit proofs within the loop for `indices` properties. */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            // All elements in `indices` are valid indices within `a`.
            forall|idx: int| 0 <= idx < indices@.len() ==> (#[trigger] indices@[idx] as int) < a@.len(),
            // All elements in `indices` correspond to non-zero values in `a`.
            forall|idx: int| 0 <= idx < indices@.len() ==> a@[indices@[idx] as int] != 0.0,
            // All non-zero elements in `a` up to `i` are included in `indices`.
            forall|j: int| 0 <= j < i ==> (a@[j] != 0.0 ==> exists|idx: int| 0 <= idx < indices@.len() && indices@[idx] as int == j),
            // `indices` contains unique elements.
            forall|idx1: int, idx2: int| 0 <= idx1 < indices@.len() && 0 <= idx2 < indices@.len() && idx1 != idx2 ==> indices@[idx1] != indices@[idx2],
            // `indices` is sorted.
            forall|idx1: int, idx2: int| 0 <= idx1 < indices@.len() && 0 <= idx2 < indices@.len() && (indices@[idx1] as int) < (indices@[idx2] as int) ==> idx1 < idx2,
            // All elements in `indices` are less than i
            forall|idx: int| 0 <= idx < indices@.len() ==> (#[trigger] indices@[idx] as int) < i,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            // Proof for maintaining sorted property and unique elements is implicitly handled by appending 'i'
            // which is strictly greater than all previous elements already added.
            indices.push(i);
            proof {
                assert(indices.len() > 0);
                assert(indices@[indices@.len() - 1] as int == i as int);
                if indices@.len() > 1 {
                    assert(indices@[indices@.len() - 2] as int < i as int);
                }
                assert forall|idx1: int, idx2: int| 0 <= idx1 < (indices@.len() as int) - 1 && idx1 < idx2 < (indices@.len() as int) - 1 && (indices@[idx1] as int) < (indices@[idx2] as int) implies idx1 < idx2 {
                    // This is handled by the invariant from the previous iteration.
                }
                assert forall|idx: int| 0 <= idx < indices@.len() implies (indices@[idx] as int) < (i + 1) {
                    if idx == (indices@.len() - 1) as int {
                        assert(indices@[idx] as int == i as int);
                        assert(i as int < (i + 1) as int);
                    } else {
                        assert(indices@[idx] as int < i as int);
                        assert(indices@[idx] as int < (i + 1) as int);
                    }
                }
            }
        }
        i = i + 1;
    }
    
    proof {
        if indices@.len() == 0 {
            assert forall|j: int| 0 <= j < a@.len() implies a@[j] == 0.0 by {
                if a@[j] != 0.0 {
                    // contradiction, means there's a non-zero element, but indices is empty.
                    // This is implicitly covered by the invariant and loop termination.
                    // The invariant `forall|j: int| 0 <= j < i ==> (a@[j] != 0.0 ==> exists|idx: int| 0 <= idx < indices@.len() && indices@[idx] as int == j)`
                    // at termination implies `forall|j: int| 0 <= j < a@.len() ==> (a@[j] != 0.0 ==> exists|idx: int| 0 <= idx < indices@.len() && indices@[idx] as int == j)`.
                    // If indices@.len() is 0, then the `exists` clause is false, so `a@[j] != 0.0` must be false.
                }
            }
        } else {
            assert(! (forall|j: int| 0 <= j < a@.len() ==> a@[j] == 0.0));
        }
    }

    indices
}
// </vc-code>

}
fn main() {}