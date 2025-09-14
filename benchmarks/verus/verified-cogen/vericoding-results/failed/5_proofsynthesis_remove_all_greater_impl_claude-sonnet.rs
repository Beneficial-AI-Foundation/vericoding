// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas to help with vec operations and invariant preservation */
proof fn vec_push_contains_lemma<T>(v: Vec<T>, x: T)
    ensures
        v.push(x)@.contains(x),
        forall |y: T| v@.contains(y) ==> v.push(x)@.contains(y),
{
}

proof fn preserve_invariant_lemma(v: Vec<i32>, result_old: Vec<i32>, new_elem: i32, i: usize, e: i32)
    requires
        0 <= i < v.len(),
        new_elem == v[i as int],
        new_elem <= e,
        forall |k:int| 0 <= k < result_old.len() ==> result_old[k] <= e && v@.contains(result_old[k]),
        forall |k:int| 0 <= k < i && v[k] <= e ==> result_old@.contains(v[k]),
    ensures
        forall |k:int| 0 <= k <= i && v[k] <= e ==> result_old.push(new_elem)@.contains(v[k]),
{
    vec_push_contains_lemma(result_old, new_elem);
}
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)

    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],

    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed proof assertions and used helper lemma to establish invariant */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            preserve_invariant_lemma(v, result, v[i], i, e);
            result.push(v[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}