// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sequence indexing to use usize instead of int casting */
fn string_lex_ge_impl(s1: String, s2: String) -> (result: bool)
    ensures result == string_lex_ge(s1@, s2@)
{
    let seq1 = s1@;
    let seq2 = s2@;
    
    if seq1.len() == 0nat {
        return true;
    }
    if seq2.len() == 0nat {
        return true;
    }
    
    let mut i: usize = 0;
    while i < seq1.len() && i < seq2.len()
        invariant
            0 <= i <= seq1.len(),
            0 <= i <= seq2.len(),
            forall|j: int| 0 <= j < i ==> seq1@[j] == seq2@[j],
        decreases seq1.len() - i
    {
        if seq1@[i] < seq2@[i] {
            return false;
        }
        if seq1@[i] > seq2@[i] {
            return true;
        }
        i += 1;
    }
    
    seq1.len() >= seq2.len()
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
    /* code modified by LLM (iteration 5): unchanged implementation */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_lex_ge(x1[j]@, x2[j]@),
    {
        let ge = string_lex_ge_impl(x1[i].clone(), x2[i].clone());
        result.push(ge);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}