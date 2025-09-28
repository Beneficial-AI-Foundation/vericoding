// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_string_lex_ge_reflexive(s: Seq<char>)
    ensures string_lex_ge(s, s),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_string_lex_ge_reflexive(s.skip(1));
    }
}

proof fn lemma_string_lex_ge_empty_left(s: Seq<char>)
    ensures string_lex_ge(s, Seq::empty()),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_string_lex_ge_empty_left(s.skip(1));
    }
}

/* helper modified by LLM (iteration 5): Fix empty right lemma implementation */
proof fn lemma_string_lex_ge_empty_right(s: Seq<char>)
    ensures string_lex_ge(Seq::<char>::empty(), s),
{
    if s.len() == 0 {
    } else {
        lemma_string_lex_ge_empty_right(s.skip(1));
    }
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
    /* code modified by LLM (iteration 5): Use spec function directly without calling it */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_lex_ge(x1[j]@, x2[j]@),
            i <= x1.len()
    {
        let s1 = x1[i].clone();
        let s2 = x2[i].clone();
        proof {
            if s1@ == s2@ {
                lemma_string_lex_ge_reflexive(s1@);
            } else if s1@ == Seq::<char>::empty() {
                lemma_string_lex_ge_empty_left(s2@);
            } else if s2@ == Seq::<char>::empty() {
                lemma_string_lex_ge_empty_right(s1@);
            }
        }
        let res = s1@.len() == 0 || s2@.len() == 0 || s1@[0] >= s2@[0] || (s1@[0] == s2@[0] && string_lex_ge(s1@.skip(1), s2@.skip(1)));
        result.push(res);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}