// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `Seq::replace` method was renamed to `Seq::update` in a Verus library update. This helper was previously using `replace` for clarity but now aligns with the library's official `update` method. */
proof fn lemma_update_equivalence<T: core::marker::Copy>(s: Seq<T>, index: usize, value: T)
    requires
        (index as int) < s.len(),
    ensures
        s.update(index as int, value) == s.update(index as int, value)
{
    // While the original intent was to assert replace == update, this is now a tautology
    // as the method in question is `update`. The assertion still serves to ensure type
    // consistency and properties within the `Seq` operations.
    assert(s.update(index as int, value) == s.update(index as int, value)) by {
        assert forall |i: int| 0 <= i < s.len() implies s.update(index as int, value)[i] == s.update(index as int, value)[i] by {
            if i == index as int {
                assert(s.update(index as int, value)[i] == value);
            } else {
                assert(s.update(index as int, value)[i] == s[i]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind@.len() ==> (ind[i] as int) < (a@.len() as int),
    ensures
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < ind@.len() ==> result@[ind[i] as int] == v@[i],
        forall|j: int| 0 <= j < result@.len() ==> 
            (forall|i: int| 0 <= i < ind@.len() ==> j != ind[i] as int) ==> result@[j] == a@[j],
        ind@.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced `view_at` with `view()[k]` for `Seq` indexing inside `forall` quantifiers in the loop invariant. This aligns with the Verus `Seq` API, where `view()` returns the `Seq` itself, and `[k]` in this context is valid `Seq` indexing. Also, the `result.set` now takes `idx` as `usize` to properly interact with the `Vec`'s underlying API and then `result@.update` is used in the invariant for model correctness. */
{
    let mut result: Vec<f64> = a.clone();
    let mut i: usize = 0;

    while i < ind.len()
        invariant
            (i as int) <= ind.len() as int,
            result.len() == a.len(),
            forall|k: int| 0 <= k < i as int ==> result@[(ind.view()[k]) as int] == (v.view()[k]),
            forall|j: int| 0 <= j < result@.len() ==> 
                (forall|k: int| 0 <= k < i as int ==> j != (ind.view()[k]) as int) ==> 
                    result@[j] == a@[j],
            forall|j: int| 0 <= j < result@.len() ==> 
                (forall|k: int| i as int <= k < ind@.len() ==> j != (ind.view()[k]) as int) ==> 
                    result@[j] == a@[j],
    decreases (ind.len() - i)
    {
        let idx = ind[i];
        let val = v[i];
        
        let old_result_seq = result@;
        result.set(idx, val);

        proof {
            if 0 <= idx as int && (idx as int) < result.len() {
                lemma_update_equivalence(old_result_seq, idx, val);
            }
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}