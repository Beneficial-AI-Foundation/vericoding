// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn string_lex_ge_exec(s1: &[char], start1: usize, s2: &[char], start2: usize) -> (result: bool)
    decreases s1.len() - start1 + s2.len() - start2
{
    /* helper modified by LLM (iteration 3): Changed parameters to use indices to avoid slicing errors */
    if start1 == s1.len() {
        true
    } else if start2 == s2.len() {
        true
    } else if s1[start1] == s2[start2] {
        string_lex_ge_exec(s1, start1 + 1, s2, start2 + 1)
    } else {
        s1[start1] >= s2[start2]
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
    /* code modified by LLM (iteration 3): Updated helper call to pass indices */
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j| 0 <= j < i ==> result[j] == string_lex_ge(x1[j]@, x2[j]@),
        decreases (x1.len() - i)
    {
        let s1_chars: Vec<char> = x1[i].chars().collect();
        let s2_chars: Vec<char> = x2[i].chars().collect();
        let b = string_lex_ge_exec(&s1_chars, 0, &s2_chars, 0);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}