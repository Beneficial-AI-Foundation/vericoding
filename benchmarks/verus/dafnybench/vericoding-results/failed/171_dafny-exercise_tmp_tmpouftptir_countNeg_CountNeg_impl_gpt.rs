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
proof fn lemma_verify_neg_step(a: &[int], i: int)
    requires
        0 <= i < a.len() as int,
    ensures
        verify_neg(a, i + 1) == verify_neg(a, i) + (if a[i] < 0 { 1nat } else { 0nat })
{
    assert(i + 1 > 0);
    assert(0 <= i && i < a.len() as int);

    assert(verify_neg(a, i + 1)
        == verify_neg(a, (i + 1) - 1) + (if a[(i + 1) - 1] < 0 { 1nat } else { 0nat }));

    assert(((i + 1) - 1) == i);
    assert(a[(i + 1) - 1] == a[i]);
}

proof fn lemma_verify_neg_upper_bound(a: &[int], i: int)
    requires
        0 <= i <= a.len() as int,
    ensures
        verify_neg(a, i) <= i as nat,
    decreases i
{
    if i <= 0 {
        assert(verify_neg(a, i) == 0nat);
    } else {
        assert(0 <= i - 1);
        assert(i - 1 <= a.len() as int);
        lemma_verify_neg_upper_bound(a, i - 1);
        let b = if a[i - 1] < 0 { 1nat } else { 0nat };
        assert(verify_neg(a, i) == verify_neg(a, i - 1) + b);
        assert(b <= 1nat);
        assert(verify_neg(a, i - 1) + b <= verify_neg(a, i - 1) + 1nat);
        assert(verify_neg(a, i - 1) <= (i - 1) as nat);
        assert(verify_neg(a, i - 1) + 1nat <= (i - 1) as nat + 1nat);
        assert((i - 1) as nat + 1nat == i as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len()
        invariant cnt == verify_neg(a, i as int)
        decreases (a.len() - i) as int
    {
        let j = i;
        let ai = a[j];
        let is_neg = ai < 0;

        proof {
            lemma_verify_neg_step(a, j as int);
        }

        if is_neg {
            proof {
                assert(j < a.len());
                lemma_verify_neg_upper_bound(a, j as int);
                assert(cnt == verify_neg(a, j as int));
                assert(cnt <= j);
                assert(cnt < a.len());
            }
            cnt = cnt + 1;
        }

        i = j + 1;

        proof {
            assert(i as int == j as int + 1);
            assert(verify_neg(a, i as int) == verify_neg(a, j as int + 1));
            assert(verify_neg(a, j as int + 1)
                == verify_neg(a, j as int) + (if a[j] < 0 { 1nat } else { 0nat }));
            if is_neg {
                assert(cnt == verify_neg(a, j as int) + 1);
            } else {
                assert(cnt == verify_neg(a, j as int));
            }
            assert(cnt == verify_neg(a, i as int));
        }
    }

    assert(i == a.len());
    cnt
}
// </vc-code>

fn main() {
}

}