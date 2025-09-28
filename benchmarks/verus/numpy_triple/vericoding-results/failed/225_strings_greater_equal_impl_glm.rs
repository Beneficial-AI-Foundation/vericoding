// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed function header formatting */
fn seq_lex_ge(s1: Seq<char>, s2: Seq<char>) -> (result: bool)
    decreases s1.len() + s2.len(),
    ensures result == string_lex_ge(s1, s2)
{
    if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        true
    } else if s1[0] == s2[0] {
        seq_lex_ge(s1.skip(1), s2.skip(1))
    } else {
        s1[0] >= s2[0]
    }
}

proof fn lemma_string_lex_ge_reflexive(s: Seq<char>)
    ensures string_lex_ge(s, s)
{
    if s.len() == 0 {
    } else {
        lemma_string_lex_ge_reflexive(s.skip(1));
    }
}

proof fn lemma_string_lex_ge_empty1(s2: Seq<char>)
    ensures string_lex_ge(Seq::empty(), s2) == true
{
}

proof fn lemma_string_lex_ge_empty2(s1: Seq<char>)
    ensures string_lex_ge(s1, Seq::empty()) == true
{
    if s1.len() == 0 {
    } else {
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
    /* code modified by LLM (iteration 5): moved comment inside function body to avoid parsing issues */
    let mut result = Vec::with_capacity(x1.len());
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_lex_ge(x1[j]@, x2[j]@),
        decreases x1.len() - i
    {
        let s1_seq = x1[i]@;
        let s2_seq = x2[i]@;
        let b = seq_lex_ge(s1_seq, s2_seq);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}