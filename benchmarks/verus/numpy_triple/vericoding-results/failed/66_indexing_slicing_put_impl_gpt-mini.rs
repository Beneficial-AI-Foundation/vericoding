// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove non-negativity of usize when cast to int */
proof fn lemma_cast_usize_int(i: usize)
    ensures
        (i as int) >= 0,
{
    assert((i as int) >= 0);
}

/* helper modified by LLM (iteration 5): relate Vec length usize to its view length int */
proof fn lemma_vec_len_cast<T>(v: &Vec<T>)
    ensures
        (v.len() as int) == v@.len(),
{
    assert((v.len() as int) == v@.len());
}

/* helper modified by LLM (iteration 5): if k < v.len() then (k as int) < v@.len() */
proof fn lemma_k_lt_seq_len<T>(k: usize, v: &Vec<T>)
    requires
        k < v.len(),
    ensures
        (k as int) < v@.len(),
{
    lemma_vec_len_cast(v);
    assert((k as int) < v@.len());
}

/* helper modified by LLM (iteration 5): element at ind[k] is within a's length by precondition */
proof fn lemma_ind_elem_in_a(k: usize, ind: &Vec<usize>, a: &Vec<f64>)
    requires
        k < ind.len(),
        forall|i: int| 0 <= i < ind@.len() ==> (ind[i] as int) < a@.len(),
    ensures
        (ind@[k as int] as int) < a@.len(),
{
    lemma_k_lt_seq_len(k, ind);
    assert((k as int) < ind@.len());
    assert((ind@[k as int] as int) < a@.len());
}

/* helper modified by LLM (iteration 5): if k < ind.len() and ind.len()==v.len() then (k as int) < v@.len() */
proof fn lemma_k_lt_v_cast<T>(k: usize, ind: &Vec<usize>, v: &Vec<T>)
    requires
        k < ind.len(),
        ind.len() == v.len(),
    ensures
        (k as int) < v@.len(),
{
    lemma_vec_len_cast(v);
    lemma_vec_len_cast(ind);
    lemma_k_lt_seq_len(k, ind);
    assert((k as int) < ind@.len());
    assert(ind@.len() == v@.len());
    assert((k as int) < v@.len());
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
{
    /* code modified by LLM (iteration 5): implement put with corrected proofs and bounds handling */
    let mut res = a.clone();
    let mut k: usize = 0;
    while k < ind.len()
        invariant
            res@.len() == a@.len(),
            forall|j: int| 0 <= j < (k as int) ==> res@[ind@[j] as int] == v@[j],
            forall|j: int| 0 <= j < res@.len() ==> (forall|i: int| 0 <= i < (k as int) ==> j != ind@[i] as int) ==> res@[j] == a@[j],
        decreases (ind.len() as int) - (k as int),
    {
        let idx = ind[k];
        lemma_k_lt_seq_len(k, &ind);
        assert((k as int) < ind@.len());
        lemma_ind_elem_in_a(k, &ind, &a);
        assert((ind@[k as int] as int) < a@.len());
        lemma_k_lt_v_cast(k, &ind, &v);
        assert((k as int) < v@.len());
        assert((idx as int) < res@.len());
        assert(idx < res.len());

        res.set(idx, v[k]);

        assert(res@.len() == a@.len());
        assert(forall|j: int| 0 <= j < ((k as int) + 1) ==> res@[ind@[j] as int] == v@[j]);
        assert(forall|j: int| 0 <= j < res@.len() ==> (forall|i: int| 0 <= i < ((k as int) + 1) ==> j != ind@[i] as int) ==> res@[j] == a@[j]);

        k = k + 1;
    }
    res
}

// </vc-code>

}
fn main() {}