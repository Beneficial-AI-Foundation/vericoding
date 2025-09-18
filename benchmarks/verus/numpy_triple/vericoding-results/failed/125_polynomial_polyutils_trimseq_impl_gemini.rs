// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed from proof fn to fn returning k */
fn find_k(s: Seq<f32>) -> (k: int)
    requires
        s.len() > 0,
        s.last() == 0.0f32,
    ensures
        0 <= k < s.len(),
        (forall|j: int| k < j < s.len() ==> s[j] == 0.0f32),
        (k > 0 ==> s[k] != 0.0f32),
    decreases s.len()
{
    let i = (s.len() - 1) as int;
    if s.len() == 1 {
        0
    } else {
        let s_prefix = s.subrange(0, i);
        if s_prefix.last() != 0.0f32 {
            let k = i - 1;
            proof {
                assert forall|j: int| k < j < s.len() implies s[j] == 0.0f32 by {
                    assert(j == i);
                    assert(s[j] == s.last());
                }
            }
            k
        } else {
            let k_rec = find_k(s_prefix);
            proof {
                assert forall|j: int| k_rec < j < s.len() implies s[j] == 0.0f32 by {
                    if j < s_prefix.len() {
                    } else {
                        assert(j == i);
                        assert(s[j] == s.last());
                    }
                }
                if k_rec > 0 {
                    assert(s[k_rec] == s_prefix[k_rec]);
                }
            }
            k_rec
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
/* code modified by LLM (iteration 5): implemented correct trimming logic using a loop */
{
    if seq.len() == 0 || seq[seq.len() - 1] != 0.0f32 {
        return seq;
    } else {
        let mut result = seq;
        let s_orig = result@;

        let k: int;
        proof {
            assert(s_orig.len() > 0);
            assert(s_orig.last() == 0.0f32);
            k = find_k(s_orig);
        }

        let mut i: usize = (k + 1) as usize;
        while i < result.len()
            invariant
                result.len() == s_orig.len(),
                (k + 1) as usize <= i <= result.len(),
                forall|j: int| 0 <= j <= k ==> result@[j] == s_orig[j],
                forall|j: int| (k + 1) <= j < i ==> result@[j] == 0.0f32,
                forall|j: int| i <= j < result.len() ==> result@[j] == s_orig[j],
        {
            result.set(i, 0.0f32);
            i = i + 1;
        }

        proof {
            assert(k > 0 ==> s_orig[k] != 0.0f32);
            assert forall|j: int| k < j < s_orig.len() implies s_orig[j] == 0.0f32 by {}
        }

        return result;
    }
}
// </vc-code>

}
fn main() {}