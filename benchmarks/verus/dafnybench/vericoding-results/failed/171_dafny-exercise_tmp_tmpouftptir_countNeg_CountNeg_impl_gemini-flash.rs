use vstd::prelude::*;

verus! {

spec fn verify_neg(a: &[int], idx: int) -> nat
    decreases idx
{
    if idx <= 0 {
        0nat
    } else {
        verify_neg(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat })
    }
}

// <vc-helpers>
fn count_neg_helper(a: &[int]) -> (cnt: usize)
    ensures
        cnt as nat == verify_neg(a, a.len() as int)
{
    let mut cnt: usize = 0;
    let mut i: usize = 0;

    #[verifier::loop_invariant]
    #[verifier::spec_before_loop(
        cnt as nat == verify_neg(a, i as int),
        i <= a.len(),
    )]
    #[verifier::decreasing(a.len() - i)]
    while i < a.len()
        invariant
            cnt as nat == verify_neg(a, i as int),
            i <= a.len(),
            0 <= i,
    {
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}

proof fn lemma_count_neg_induction(a: Seq<int>, idx: nat)
    requires
        idx <= a.len(),
    ensures
        count_neg_helper_seq(a.subsequence(0, idx as int)) as nat == verify_neg_seq(a, idx as int),
{
    if idx == 0 {
        assert(count_neg_helper_seq(a.subsequence(0, 0)) == 0);
        assert(verify_neg_seq(a, 0) == 0);
    } else {
        lemma_count_neg_induction(a, (idx - 1) as nat);
        let val_at_idx_minus_1 = a[(idx - 1) as int];
        if val_at_idx_minus_1 < 0 {
            assert(count_neg_helper_seq(a.subsequence(0, idx as int)) == count_neg_helper_seq(a.subsequence(0, (idx - 1) as int)) + 1);
            assert(verify_neg_seq(a, idx as int) == verify_neg_seq(a, (idx - 1) as int) + 1);
        } else {
            assert(count_neg_helper_seq(a.subsequence(0, idx as int)) == count_neg_helper_seq(a.subsequence(0, (idx - 1) as int)));
            assert(verify_neg_seq(a, idx as int) == verify_neg_seq(a, (idx - 1) as int));
        }
    }
}

spec fn verify_neg_seq(a: Seq<int>, idx: int) -> nat
    decreases idx
{
    if idx <= 0 {
        0nat
    } else {
        verify_neg_seq(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat })
    }
}

fn count_neg_helper_seq(a: Seq<int>) -> (cnt: usize)
    ensures cnt as nat == verify_neg_seq(a, a.len() as int)
{
    let mut cnt: usize = 0;
    let mut i: usize = 0;

    #[verifier::loop_invariant]
    #[verifier::spec_before_loop(
        cnt as nat == verify_neg_seq(a, i as int),
        i <= a.len(),
    )]
    #[verifier::decreasing(a.len() - i)]
    while i < a.len()
        invariant
            cnt as nat == verify_neg_seq(a, i as int),
            i <= a.len(),
            0 <= i,
    {
        if a[i as int] < 0 { // Corrected: Use 'i as int' for indexing a Seq<int>
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    count_neg_helper(a)
}
// </vc-code>

fn main() {
}

}