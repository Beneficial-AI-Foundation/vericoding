// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): reflexivity of string_lex_ge */
fn lemma_string_lex_ge_reflexive(s: Seq<char>)
    ensures
        string_lex_ge(s, s),
    decreases s.len()
{
    if s.is_empty() {
        // base case: empty sequence is >= itself
    } else {
        lemma_string_lex_ge_reflexive(s.skip(1));
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
    /* code modified by LLM (iteration 5): elementwise lexicographic comparison using spec function */
    // impl-start
    let n: usize = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j as usize] == string_lex_ge(x1[j as usize]@, x2[j as usize]@),
        decreases (n as int - i as int)
    {
        let s1 = x1[i]@;
        let s2 = x2[i]@;
        let b = string_lex_ge(s1, s2);
        result.push(b);
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>


}
fn main() {}