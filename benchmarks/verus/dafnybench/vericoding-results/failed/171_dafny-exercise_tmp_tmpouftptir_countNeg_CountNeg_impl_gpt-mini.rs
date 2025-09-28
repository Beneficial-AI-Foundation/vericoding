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
proof fn lemma_verify_neg_succ(a: &[int], idx: int)
    requires 0 < idx && idx <= a.len() as int
    ensures verify_neg(a, idx) == verify_neg(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat })
    decreases idx
{
    reveal(verify_neg);
    assert(verify_neg(a, idx) ==
        if idx <= 0 {
            0nat
        } else {
            verify_neg(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat })
        });
    assert(0 < idx);
    assert(!(idx <= 0));
    assert(verify_neg(a, idx) == verify_neg(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat }));
}
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut cnt: usize = 0usize;
    while (i < a.len())
        invariant (i as int) <= (a.len() as int)
        invariant (cnt as nat) == verify_neg(a, i as int)
        decreases a.len() - i
    {
        let old_cnt = cnt;
        assert((old_cnt as nat) == verify_neg(a, i as int));
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        proof {
            // i < a.len() implies (i + 1) as int <= a.len() as int and (i + 1) > 0
            lemma_verify_neg_succ(a, (i + 1) as int);
        }
        assert((cnt as nat) == verify_neg(a, (i + 1) as int));
        i = i + 1;
    }
    cnt
}
// </vc-code>

fn main() {
}

}