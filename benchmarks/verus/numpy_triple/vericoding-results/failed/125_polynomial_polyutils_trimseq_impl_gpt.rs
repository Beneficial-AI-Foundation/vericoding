// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed existential witness syntax and completed forall/existence proofs */
proof fn lemma_suffix_zero_exists_k(s: Seq<f32>)
    requires
        s.len() > 0,
        s[s.len() - 1] == 0.0f32
    ensures
        exists|k: int|
            0 <= k < s.len()
            && (forall|j: int| k < j < s.len() ==> s[j] == 0.0f32)
            && (k > 0 ==> s[k] != 0.0f32)
    decreases s.len()
{
    let n = s.len();
    if n == 1 {
        assert(0 <= 0 && 0 < n);
        assert forall |j: int| 0 < j < n implies s[j] == 0.0f32 by { };
        assert(exists|k: int|
            0 <= k < n
            && (forall|j: int| k < j < n ==> s[j] == 0.0f32)
            && (k > 0 ==> s[k] != 0.0f32)
        ) by {
            let k: int = 0;
            assert(0 <= k && k < n);
            assert forall |j: int| k < j < n implies s[j] == 0.0f32 by { };
            assert(k > 0 ==> s[k] != 0.0f32);
        };
    } else {
        let k1: int = n - 2;
        if s[k1] != 0.0f32 {
            assert(0 <= k1 && k1 < n);
            assert forall |j: int| k1 < j < n implies s[j] == 0.0f32 by {
                // Since k1 = n - 2 and j is int with k1 < j < n, we must have j = n - 1
                assert(j > n - 2);
                assert(j >= n - 1);
                assert(j < n);
                assert(j <= n - 1);
                assert(j == n - 1);
                assert(s[n - 1] == 0.0f32);
            };
            assert(exists|k: int|
                0 <= k < n
                && (forall|j: int| k < j < n ==> s[j] == 0.0f32)
                && (k > 0 ==> s[k] != 0.0f32)
            ) by {
                let k: int = k1;
                assert(0 <= k && k < n);
                assert forall |j: int| k < j < n implies s[j] == 0.0f32 by {
                    assert(j > n - 2);
                    assert(j >= n - 1);
                    assert(j < n);
                    assert(j <= n - 1);
                    assert(j == n - 1);
                    assert(s[n - 1] == 0.0f32);
                };
                assert(k > 0 ==> s[k] != 0.0f32) by { if k > 0 { assert(s[k] != 0.0f32); } };
            };
        } else {
            let p = s.take(n - 1);
            assert(p.len() == n - 1);
            lemma_suffix_zero_exists_k(p);
            let k2 = choose|k: int|
                0 <= k < p.len()
                && (forall|j: int| k < j < p.len() ==> p[j] == 0.0f32)
                && (k > 0 ==> p[k] != 0.0f32);
            assert(0 <= k2 && k2 < n - 1);
            assert forall |j: int| k2 < j < n implies s[j] == 0.0f32 by {
                if j < n - 1 {
                    assert(k2 < j && j < p.len());
                    assert(p[j] == 0.0f32);
                    assert(p[j] == s[j]);
                } else {
                    assert(j == n - 1);
                    assert(s[j] == 0.0f32);
                }
            };
            assert(k2 > 0 ==> s[k2] != 0.0f32) by {
                if k2 > 0 {
                    assert(p[k2] != 0.0f32);
                    assert(p[k2] == s[k2]);
                }
            };
            assert(exists|k: int|
                0 <= k < n
                && (forall|j: int| k < j < n ==> s[j] == 0.0f32)
                && (k > 0 ==> s[k] != 0.0f32)
            ) by {
                let k: int = k2;
                assert(0 <= k && k < n);
                assert forall |j: int| k < j < n implies s[j] == 0.0f32 by {
                    if j < n - 1 {
                        assert(k < j && j < p.len());
                        assert(p[j] == 0.0f32);
                        assert(p[j] == s[j]);
                    } else {
                        assert(j == n - 1);
                        assert(s[j] == 0.0f32);
                    }
                };
                assert(k > 0 ==> s[k] != 0.0f32) by {
                    if k > 0 {
                        assert(p[k] != 0.0f32);
                        assert(p[k] == s[k]);
                    }
                };
            };
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),

        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,

        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>

            exists|k: int| 
                0 <= k < seq.len() &&

                (forall|j: int| k < j < seq.len() ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return input vector unchanged and invoke lemma to establish existential when needed */
    let n = seq.len();
    if n == 0 {
        return seq;
    }
    let last_zero = seq[n - 1] == 0.0f32;
    let ghost s_view = seq@;
    let result_vec = seq;
    proof { assert(result_vec@ == s_view); }
    if last_zero {
        proof { lemma_suffix_zero_exists_k(s_view); }
    }
    result_vec
}
// </vc-code>

}
fn main() {}