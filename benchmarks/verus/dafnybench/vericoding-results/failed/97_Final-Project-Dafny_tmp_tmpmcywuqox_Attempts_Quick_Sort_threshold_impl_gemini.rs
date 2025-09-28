// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced while-loop helpers with recursive spec functions for partitioning */
spec fn filter_le(seq: Seq<int>, thres: int) -> (res: Seq<int>)
    decreases seq.len()
    ensures res.to_multiset() == seq.to_multiset().filter(|x: int| x <= thres)
{
    if seq.len() == 0 {
        Seq::new()
    } else {
        let elem = seq.last();
        let rest_filtered = filter_le(seq.drop_last(), thres);
        if elem <= thres {
            rest_filtered.push(elem)
        } else {
            rest_filtered
        }
    }
}

spec fn filter_gt(seq: Seq<int>, thres: int) -> (res: Seq<int>)
    decreases seq.len()
    ensures res.to_multiset() == seq.to_multiset().filter(|x: int| x > thres)
{
    if seq.len() == 0 {
        Seq::new()
    } else {
        let elem = seq.last();
        let rest_filtered = filter_gt(seq.drop_last(), thres);
        if elem > thres {
            rest_filtered.push(elem)
        } else {
            rest_filtered
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn threshold(thres: int, seq: Seq<int>) -> (ret: (Seq<int>, Seq<int>))
    ensures 
        (forall|x: int| ret.0.contains(x) ==> x <= thres) &&
        (forall|x: int| ret.1.contains(x) ==> x >= thres) &&
        ret.0.len() + ret.1.len() == seq.len() &&
        ret.0.to_multiset().add(ret.1.to_multiset()) == seq.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): changed implementation to use recursive spec functions to correctly handle ghost types */
{
    let ret = (filter_le(seq, thres), filter_gt(seq, thres));
    proof {
        vstd::multiset::lemma_multiset_filter_complement(seq.to_multiset(), |x: int| x <= thres);
    }
    ret
}
// </vc-code>

}
fn main() {}