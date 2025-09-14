// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove invalid methods and fix helpers */
spec fn is_elem_in_vec(v: Seq<i32>, elem: i32) -> bool {
    exists|k: int| 0 <= k < v.len() && v[k] == elem
}

proof fn lemma_seq_contains_subseq<T>(v: Seq<T>, sub: Seq<T>, elem: T)
    requires
        sub =~= v,
        sub.contains(elem)
    ensures
        v.contains(elem)
{}

proof fn lemma_seq_slice_contains<T>(v: Seq<T>, i: int, j: int, elem: T)
    requires
        0 <= i <= j <= v.len(),
        v.subrange(i, j).contains(elem)
    ensures
        v.contains(elem)
{}

proof fn lemma_vec_contains_index<T>(v: Vec<T>, idx: int)
    requires
        0 <= idx < v.len() as int
    ensures
        v@.contains(v@[idx])
{}

proof fn lemma_vec_push_contains<T>(v: Vec<T>, elem: T)
    ensures
        v.push(elem)@.contains(elem)
{}

proof fn lemma_vec_push_preserves_contains<T>(v: Vec<T>, elem: T, existing: Seq<T>)
    requires
        forall |k: int| 0 <= k < existing.len() ==> v@.contains(existing[k])
    ensures
        forall |k: int| 0 <= k < existing.len() ==> v.push(elem)@.contains(existing[k])
{}
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
/* code modified by LLM (iteration 5): Fix verification errors and indexing */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k: int| 0 <= k < result@.len() ==> result@[k] <= e,
            forall |k: int| 0 <= k < result@.len() ==> v@.contains(result@[k]),
            forall |k: int| 0 <= k < i && v[k as usize] <= e ==> result@.contains(v[k as usize])
        decreases v.len() - i
    {
        if v[i] <= e {
            proof {
                lemma_vec_contains_index(v, i as int);
            }
            result.push(v[i]);
            proof {
                lemma_vec_push_contains(result, v[i]);
                lemma_vec_push_preserves_contains(result, v[i], result@);
            }
        }
        i += 1;
    }
    
    proof {
        assert forall |k: int| 0 <= k < v.len() && v[k as usize] <= e implies result@.contains(v[k as usize]) by {
            let k_val = k;
            if k_val < i as int {
                assert(result@.contains(v[k_val as usize]));
            } else {
                assert(false);
            }
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}