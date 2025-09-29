// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn total_elems(seqs: Seq<Seq<i8>>) -> nat
    decreases seqs.len()
{
    if seqs.len() == 0 {
        0
    } else {
        seqs[0].len() + total_elems(seqs.drop_first())
    }
}

pub proof fn lemma_total_elems_nonneg(seqs: Seq<Seq<i8>>)
    ensures
        total_elems(seqs) >= 0,
    decreases seqs.len()
{
    if seqs.len() == 0 {
    } else {
        lemma_total_elems_nonneg(seqs.drop_first());
    }
}

/* helper modified by LLM (iteration 2): added spec function over Seq<Vec<i8>> computing total elements */
pub open spec fn total_elems_vecs(seqs: Seq<Vec<i8>>) -> nat
    decreases seqs.len()
{
    if seqs.len() == 0 {
        0
    } else {
        seqs[0]@.len() + total_elems_vecs(seqs.drop_first())
    }
}

/* helper modified by LLM (iteration 2): lemma proving non-negativity for total_elems_vecs */
pub proof fn lemma_total_elems_vecs_nonneg(seqs: Seq<Vec<i8>>)
    ensures
        total_elems_vecs(seqs) >= 0,
    decreases seqs.len()
{
    if seqs.len() == 0 {
    } else {
        lemma_total_elems_vecs_nonneg(seqs.drop_first());
    }
}
// </vc-helpers>

// <vc-spec>
fn savez_compressed(filename: &str, arrays: &Vec<Vec<i8>>) -> (result: ())
    requires 
        filename@.len() > 0,
        arrays@.len() > 0,
    ensures
        /* File creation and data preservation properties are ensured */
        true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call lemma adapted for Seq<Vec<i8>> to avoid type mismatch */
    proof {
        lemma_total_elems_vecs_nonneg(arrays@);
    }
}
// </vc-code>


}
fn main() {}