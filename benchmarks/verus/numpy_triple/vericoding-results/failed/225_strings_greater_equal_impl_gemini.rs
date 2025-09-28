// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed 'lemma' syntax to 'proof fn' */
#[verifier::spinoff_prover]
proof fn string_lex_ge_refl(s: Seq<char>)
    ensures string_lex_ge(s, s),
    decreases s.len()
{
    if s.len() > 0 {
        string_lex_ge_refl(s.skip(1));
    }
}

/* helper modified by LLM (iteration 4): fixed 'lemma' syntax to 'proof fn' */
#[verifier::spinoff_prover]
proof fn string_lex_ge_prefix_lemma(s1: Seq<char>, s2: Seq<char>, i: nat)
    requires
        i <= s1.len(),
        i <= s2.len(),
        s1.subrange(0, i as int) == s2.subrange(0, i as int),
    ensures
        string_lex_ge(s1, s2) == string_lex_ge(s1.skip(i as int), s2.skip(i as int)),
    decreases i
{
    if i > 0 {
        assert(s1.len() > 0 && s2.len() > 0 && s1[0] == s2[0]);
        string_lex_ge_prefix_lemma(s1.skip(1), s2.skip(1), (i - 1) as nat);
    }
}

fn string_lex_ge_exec(s1: &String, s2: &String) -> (result: bool)
    ensures result == string_lex_ge(s1@, s2@)
{
    let s1_slice = s1.as_str();
    let s2_slice = s2.as_str();
    let len1 = s1_slice.len();
    let len2 = s2_slice.len();
    let min_len = if len1 < len2 { len1 } else { len2 };

    let mut i: usize = 0;
    while i < min_len
        invariant
            i <= min_len,
            s1_slice@.subrange(0, i as int) == s2_slice@.subrange(0, i as int),
    {
        let c1 = s1_slice.get_char(i);
        let c2 = s2_slice.get_char(i);
        if c1 != c2 {
            proof {
                string_lex_ge_prefix_lemma(s1_slice@, s2_slice@, i as nat);
            }
            return c1 >= c2;
        }
        i = i + 1;
    }

    proof {
        string_lex_ge_prefix_lemma(s1_slice@, s2_slice@, min_len as nat);
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
spec fn string_lex_ge(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        true
    } else if s1[0] == s2[0] {
        string_lex_ge(s1.skip(1), s2.skip(1))
    } else {
        s1[0] >= s2[0]
    }
}

fn greater_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == string_lex_ge(x1[i]@, x2[i]@),
        /* Reflexive property: every string is >= itself */
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == true,
        /* Empty string properties */
        forall|i: int| 0 <= i < result.len() && x1[i]@ == Seq::<char>::empty() && x2[i]@ == Seq::<char>::empty() ==> result[i] == true,
        forall|i: int| 0 <= i < result.len() && x1[i]@ != Seq::<char>::empty() && x2[i]@ == Seq::<char>::empty() ==> result[i] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error in loop invariant by removing 'as usize' cast */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    let len = x1.len();
    while i < len
        invariant
            x1.len() == len,
            x1.len() == x2.len(),
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == string_lex_ge(x1[j]@, x2[j]@),
    {
        let ge = string_lex_ge_exec(&x1[i], &x2[i]);
        result.push(ge);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}