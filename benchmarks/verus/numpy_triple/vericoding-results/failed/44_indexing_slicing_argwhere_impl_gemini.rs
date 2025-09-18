// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove non-containment */
proof fn not_contains_if_all_less(s: Seq<usize>, x: usize)
    requires forall |i: int| 0 <= i < s.len() ==> s[i] < x
    ensures !s.contains(x)
{
    if s.contains(x) {
        choose |i: int| 0 <= i < s.len() && s[i] == x;
        assert(s[i] == x);
        assert(s[i] < x);
        assert(x < x);
    }
}
// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (#[trigger] indices[i]) < a.len(),
        forall|i: int| 0 <= i < indices.len() ==> a[indices[i] as int] != 0.0,
        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == i,
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && i != j ==> indices[i] != indices[j],
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && (indices[i] as int) < (indices[j] as int) ==> i < j,
        (indices.len() == 0) == (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof blocks for invariant and postcondition */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < indices.len() ==> (#[trigger]indices@[j]) < i,
            forall|j1: int, j2: int| 0 <= j1 < j2 < indices.len() ==> indices@[j1] < indices@[j2],
            forall|k: int| 0 <= k < (i as int) ==> ((a@[k] != 0.0) <==> indices@.contains(k as usize)),
        decreases a.len() - i
    {
        let old_indices = indices@;
        if a[i] != 0.0 {
            indices.push(i);
            proof {
                assert forall|k: int| 0 <= k < i implies (indices@.contains(k as usize) <==> old_indices.contains(k as usize)) by {
                    vstd::seq_lib::lemma_push_contains_other(old_indices, i as usize, k as usize);
                }
                vstd::seq_lib::lemma_push_contains(old_indices, i as usize);
            }
        } else {
            proof {
                not_contains_if_all_less(indices@, i);
                assert(!indices@.contains(i as usize));
            }
        }
        i = i + 1;
    }

    proof {
        if forall|k: int| 0 <= k < a.len() ==> a[k] == 0.0 {
            assert forall|k: int| 0 <= k < a.len() implies !indices@.contains(k as usize) by {
                assert(a@[k] == 0.0);
                assert((a@[k] != 0.0) <==> indices@.contains(k as usize));
            };
            if indices.len() > 0 {
                let val = indices@[0];
                assert(indices@.contains(val));
                assert(val < a.len());
                let witness = val as int;
                assert(!indices@.contains(witness as usize));
                assert(false);
            }
            assert(indices.len() == 0);
        } else {
            assert(exists|k: int| 0 <= k < a.len() && a[k] != 0.0);
        }

        if indices.len() == 0 {
            assert forall|k: int| 0 <= k < a.len() implies a[k] == 0.0 by {
                assert(!indices@.contains(k as usize));
                assert((a@[k] != 0.0) <==> indices@.contains(k as usize));
            };
        }
    }

    indices
}
// </vc-code>

}
fn main() {}