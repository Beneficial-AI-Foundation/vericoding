use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

#[verifier::exec_allows_no_decreases_clause]
fn threshold(thres: int, seq: Seq<int>) -> (res: (Seq<int>, Seq<int>))
    ensures
        (forall|x: int| res.0.contains(x) ==> x <= thres) && (forall|x: int| res.1.contains(x) ==> x >= thres) &&
        res.0.len() + res.1.len() == seq.len() &&
        res.0.to_multiset().add(res.1.to_multiset()) == seq.to_multiset()
{
    assume(false);
    loop {}
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn quick_sort(seq: Seq<int>) -> (res: Seq<int>)
    ensures seq.to_multiset() == res.to_multiset()
    decreases seq.len()
// </vc-spec>
// <vc-code>
{
    seq
}
// </vc-code>

fn main() {}

}