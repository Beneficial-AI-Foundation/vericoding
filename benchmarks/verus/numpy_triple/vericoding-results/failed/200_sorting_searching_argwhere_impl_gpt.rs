// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove push preserves prefix elements */
proof fn lemma_seq_push_preserves_prefix(s: Seq<usize>, x: usize)
    ensures
        forall|j: int| 0 <= j < s.len() ==> s.push(x)[j] == s[j],
{
    assert(s.push(x).len() == s.len() + 1);
    assert forall|j: int| 0 <= j < s.len() implies s.push(x)[j] == s[j] by
    {
        assert(0 <= j && j < s.push(x).len());
        assert(s.push(x)[j] == s[j]);
    };
}

/* helper modified by LLM (iteration 5): show contains is preserved by push */
proof fn lemma_seq_push_preserves_contains(s: Seq<usize>, x: usize, y: usize)
    ensures
        s.contains(y) ==> s.push(x).contains(y),
{
    if s.contains(y) {
        let j = choose|j: int| 0 <= j < s.len() && s[j] == y;
        lemma_seq_push_preserves_prefix(s, x);
        assert(s.push(x).len() == s.len() + 1);
        assert(0 <= j && j < s.push(x).len());
        assert(s.push(x)[j] == s[j]);
        assert(s.push(x)[j] == y);
        assert(exists|w: int| 0 <= w < s.push(x).len() && s.push(x)[w] == y);
    }
}

/* helper modified by LLM (iteration 5): show strict increasing preserved when appending larger element */
proof fn lemma_seq_push_preserves_strict_increasing(s: Seq<usize>, k: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] < k,
    ensures
        forall|i: int, j: int| 0 <= i < j < s.push(k).len() ==> s.push(k)[i] < s.push(k)[j],
{
    lemma_seq_push_preserves_prefix(s, k);
    assert(s.push(k).len() == s.len() + 1);
    assert forall|i: int, j: int| 0 <= i < j < s.push(k).len() implies s.push(k)[i] < s.push(k)[j] by
    {
        if j < s.len() {
            assert(0 <= i && i < j && j < s.len());
            assert(s.push(k)[i] == s[i]);
            assert(s.push(k)[j] == s[j]);
        } else {
            assert(j == s.len());
            if i < s.len() {
                assert(s.push(k)[i] == s[i]);
                assert(s.push(k)[j] == k);
                assert(s[i] < k);
            } else {
                // impossible: i cannot be >= s.len() while i < j == s.len()
            }
        }
    };
}

/* helper modified by LLM (iteration 5): last element after push is the pushed value */
proof fn lemma_seq_push_last_is_x(s: Seq<usize>, x: usize)
    ensures
        s.push(x)[s.len()] == x,
{
    assert(s.push(x).len() == s.len() + 1);
    assert(s.len() < s.push(x).len());
    assert(s.push(x)[s.len()] == x);
}
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices@.len() ==> 
            indices@[i] < a@.len() && a@[indices@[i] as int] != 0.0,

        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] != indices@[j],

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] < indices@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected int/usize casts and sequence len usage; maintain sorted nonzero indices */
    let n = a.len();
    let mut indices: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k as int <= a@.len(),
            forall|i: int| 0 <= i < indices@.len() ==> indices@[i] < k && a@[indices@[i] as int] != 0.0,
            forall|i: int| 0 <= i < k as int && a@[i] != 0.0 ==> indices@.contains(i as usize),
            forall|i: int, j: int| 0 <= i < j < indices@.len() ==> indices@[i] < indices@[j],
        decreases a@.len() - (k as int)
    {
        let k0 = k;
        let ghost old_seq = indices@;
        proof {
            assert forall|t: int|
                0 <= t < old_seq.len() implies old_seq[t] < k0 && a@[old_seq[t] as int] != 0.0 by
            {
                assert(0 <= t && t < indices@.len());
                assert(old_seq == indices@);
            };
            assert forall|i: int, j: int|
                0 <= i < j < old_seq.len() implies old_seq[i] < old_seq[j] by
            {
                assert(0 <= i && i < j && j < indices@.len());
                assert(old_seq == indices@);
            };
            assert forall|i: int|
                0 <= i < k0 as int && a@[i] != 0.0 implies old_seq.contains(i as usize) by
            {
                assert(old_seq == indices@);
            };
        }
        if a[k0] != 0.0 {
            indices.push(k0);
        }
        k = k0 + 1;
        proof {
            if a@[k0 as int] != 0.0 {
                assert(indices@ == old_seq.push(k0));
                assert forall|i: int|
                    0 <= i < k0 as int && a@[i] != 0.0 implies indices@.contains(i as usize) by
                {
                    assert(old_seq.contains(i as usize));
                    lemma_seq_push_preserves_contains(old_seq, k0, i as usize);
                    assert(old_seq.push(k0).contains(i as usize));
                    assert(indices@ == old_seq.push(k0));
                };
                let j = old_seq.len();
                lemma_seq_push_last_is_x(old_seq, k0);
                assert(0 <= j && j < indices@.len());
                assert(indices@[j] == k0);
                assert(indices@.contains(k0));

                assert forall|t: int|
                    0 <= t < indices@.len() implies indices@[t] < k && a@[indices@[t] as int] != 0.0 by
                {
                    if t < old_seq.len() {
                        lemma_seq_push_preserves_prefix(old_seq, k0);
                        assert(indices@ == old_seq.push(k0));
                        assert(indices@[t] == old_seq[t]);
                        assert(old_seq[t] < k0);
                        assert(old_seq[t] < k);
                        assert(a@[old_seq[t] as int] != 0.0);
                    } else {
                        assert(t == old_seq.len());
                        lemma_seq_push_last_is_x(old_seq, k0);
                        assert(indices@ == old_seq.push(k0));
                        assert(indices@[t] == k0);
                        assert(k0 < k);
                        assert(a@[k0 as int] != 0.0);
                    }
                };

                lemma_seq_push_preserves_strict_increasing(old_seq, k0);
                assert forall|i: int, j: int|
                    0 <= i < j < indices@.len() implies indices@[i] < indices@[j] by
                {
                    if j < old_seq.len() {
                        lemma_seq_push_preserves_prefix(old_seq, k0);
                        assert(indices@ == old_seq.push(k0));
                        assert(indices@[i] == old_seq[i]);
                        assert(indices@[j] == old_seq[j]);
                    } else {
                        assert(j == old_seq.len());
                        if i < old_seq.len() {
                            lemma_seq_push_preserves_prefix(old_seq, k0);
                            lemma_seq_push_last_is_x(old_seq, k0);
                            assert(indices@ == old_seq.push(k0));
                            assert(indices@[i] == old_seq[i]);
                            assert(indices@[j] == k0);
                            assert(old_seq[i] < k0);
                        }
                    }
                };
            } else {
                assert(indices@ == old_seq);
                assert forall|i: int|
                    0 <= i < k0 as int && a@[i] != 0.0 implies indices@.contains(i as usize) by
                {
                    assert(old_seq.contains(i as usize));
                    assert(indices@ == old_seq);
                };

                assert forall|t: int|
                    0 <= t < indices@.len() implies indices@[t] < k && a@[indices@[t] as int] != 0.0 by
                {
                    assert(indices@ == old_seq);
                    assert(indices@[t] == old_seq[t]);
                    assert(old_seq[t] < k0);
                    assert(indices@[t] < k0);
                    assert(indices@[t] < k);
                    assert(a@[indices@[t] as int] != 0.0);
                };

                assert forall|i: int, j: int|
                    0 <= i < j < indices@.len() implies indices@[i] < indices@[j] by
                {
                    assert(indices@ == old_seq);
                    assert(indices@[i] == old_seq[i]);
                    assert(indices@[j] == old_seq[j]);
                };
            }
        }
    }
    indices
}
// </vc-code>

}
fn main() {}