// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemmas about Seq.push indexing (prefix and last element) */
proof fn lemma_seq_push_preserves_prefix<T>(s: Seq<T>, a: T, j: int)
    requires
        0 <= j,
        j < s.len(),
    ensures
        (s.push(a))[j] == s[j],
{
}

proof fn lemma_seq_push_last_index<T>(s: Seq<T>, a: T)
    ensures
        (s.push(a))[s.len()] == a,
{
}
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix assert_forall_by binder usage and maintain invariant via Seq.push lemmas */
    let mut res: Vec<bool> = Vec::new();
    while res.len() < x.len()
        invariant
            res.len() <= x.len(),
            forall|j: int| 0 <= j < res.len() ==> #[trigger] res@[j] == (x@[j] == 0.0),
        decreases x.len() - res.len()
    {
        let i = res.len();
        let b: bool = x[i] == 0.0;
        let ghost old_seq = res@;
        proof {
            assert(res.len() == i);
            assert(old_seq == res@);
            assert_forall_by(|j: int| {
                requires 0 <= j && j < i,
                ensures old_seq[j] == (x@[j] == 0.0),
            }, {
                assert(0 <= j && j < i);
                assert(old_seq == res@);
                assert(#[trigger] res@[j] == (x@[j] == 0.0));
                assert(old_seq[j] == res@[j]);
            });
        }
        res.push(b);
        proof {
            assert(i < x.len());
            assert(x@[i] == x[i]);
            assert(res@ == old_seq.push(b));
            let new_len = res.len();
            assert(new_len == i + 1);
            assert_forall_by(|j: int| {
                requires 0 <= j && j < new_len,
                ensures #[trigger] res@[j] == (x@[j] == 0.0),
            }, {
                assert(0 <= j && j < new_len);
                if j < i {
                    lemma_seq_push_preserves_prefix::<bool>(old_seq, b, j);
                    assert(res@ == old_seq.push(b));
                    assert(res@[j] == (old_seq.push(b))[j]);
                    assert(res@[j] == old_seq[j]);
                    assert(old_seq[j] == (x@[j] == 0.0));
                    assert(#[trigger] res@[j] == (x@[j] == 0.0));
                } else {
                    assert(j == i);
                    lemma_seq_push_last_index::<bool>(old_seq, b);
                    assert(res@ == old_seq.push(b));
                    assert(res@[j] == (old_seq.push(b))[i]);
                    assert(res@[j] == b);
                    assert(b == (x@[i] == 0.0));
                    assert(#[trigger] res@[j] == (x@[j] == 0.0));
                }
            });
        }
    }
    res
}
// </vc-code>

}
fn main() {}