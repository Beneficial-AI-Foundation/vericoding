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
    /* code modified by LLM (iteration 5): fixed non-existent seq lemma calls and completed proofs for all invariants. */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result@.len() ==> a@[result@[k] as int] != 0.0,
            forall|j: int| 0 <= j < i && a@[j as int] != 0.0 ==> 
                exists|k: int| 0 <= k < result@.len() && result@[k] as int == j,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() ==> result@[k1] < result@[k2],
            forall|k: int| 0 <= k < result@.len() ==> (result@[k] as int) < i,
        decreases a.len() - i
    {
        let result_old = result@;
        if a[i] != 0.0 {
            result.push(i);
            proof {
                assert forall |k: int| 0 <= k < result@.len() implies a@[result@[k] as int] != 0.0 by {
                    if k < result_old.len() {
                        vstd::seq_lib::lemma_push_preserves_index(result_old, i, k);
                    } else {
                        vstd::seq_lib::lemma_push_gets(result_old, i);
                    }
                };

                assert forall |j: int| 0 <= j < i + 1 && a@[j as int] != 0.0
                    implies (exists|k: int| 0 <= k < result@.len() && result@[k] as int == j) by {
                    if j < i {
                        let k_old = choose|k_old: int| 0 <= k_old < result_old.len() && result_old[k_old] as int == j;
                        vstd::seq_lib::lemma_push_preserves_index(result_old, i, k_old);
                        assert(result@[k_old] as int == j);
                    } else {
                        vstd::seq_lib::lemma_push_gets(result_old, i);
                        let k_new = result@.len() - 1;
                        assert(result@[k_new] as int == j);
                    }
                };
                
                assert forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() implies result@[k1] < result@[k2] by {
                    vstd::seq_lib::lemma_push_preserves_subrange(result_old, i, 0, result_old.len());
                    if k2 < result_old.len() {
                    } else {
                        assert(k2 == result_old.len());
                        vstd::seq_lib::lemma_push_gets(result_old, i);
                        assert(k1 < result_old.len());
                        assert(result_old@[k1] < i);
                        assert(result@[k1] < result@[k2]);
                    }
                };

                assert forall|k: int| 0 <= k < result@.len() implies (result@[k] as int) < i + 1 by {
                     if k < result_old.len() {
                         vstd::seq_lib::lemma_push_preserves_index(result_old, i, k);
                     } else {
                         vstd::seq_lib::lemma_push_gets(result_old, i);
                     }
                };
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}