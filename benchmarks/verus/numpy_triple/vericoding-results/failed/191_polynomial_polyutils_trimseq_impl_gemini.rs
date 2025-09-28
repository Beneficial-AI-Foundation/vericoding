// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error by adding `by {}` to `assert forall`. */
proof fn find_k_recursive(s: Seq<f32>, i: int) -> (k: int)
    requires
        0 <= i < s.len() as int,
        forall|j: int| i < j < s.len() as int ==> s[j] == 0.0f32,
    ensures
        0 <= k <= i,
        forall|j: int| k < j < s.len() as int ==> s[j] == 0.0f32,
        k > 0 ==> s[k] != 0.0f32,
    decreases i
{
    if s[i] != 0.0f32 {
        i
    } else if i > 0 {
        assert forall|j: int| i - 1 < j < s.len() as int implies s[j] == 0.0f32 by {};
        find_k_recursive(s, i - 1)
    } else {
        0
    }
}

/* helper modified by LLM (iteration 5): No changes were needed for this helper. */
proof fn find_last_nonzero_lemma(s: Seq<f32>) -> (k: int)
    requires
        s.len() > 0,
        s[s.len() - 1] == 0.0f32,
    ensures
        0 <= k < s.len() as int,
        forall|j: int| k < j < s.len() as int ==> s[j] == 0.0f32,
        k > 0 ==> s[k] != 0.0f32,
{
    let i = s.len() as int - 1;
    let k = find_k_recursive(s, i);
    k
}
// </vc-helpers>

// <vc-spec>
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),

        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,

        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>

            exists|k: int| 
                0 <= k < seq.len() as int &&

                (forall|j: int| k < j < seq.len() as int ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() as int ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Previous logic was sound; failure was due to a compile error in a helper. */
    let result = seq.clone();
    if seq.len() > 0 && seq[seq.len() - 1] == 0.0f32 {
        proof {
            assert(seq@.len() > 0 && seq@[seq@.len() - 1] == 0.0f32);
            find_last_nonzero_lemma(seq@);
        }
    }
    result
}
// </vc-code>

}
fn main() {}