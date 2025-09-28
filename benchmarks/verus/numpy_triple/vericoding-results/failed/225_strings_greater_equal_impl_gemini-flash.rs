// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected type errors for `s1.skip(1)` and `s2.skip(1)` arguments by casting to `int` and replaced direct indexing with `@` for sequence access. Also ensured consistency with spec function string_lex_ge by calling it instead of itself. */
fn string_lex_ge_helper(s1: Seq<char>, s2: Seq<char>) -> (res: bool)
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        true
    } else if s1@[0] == s2@[0] {
        string_lex_ge(s1.skip(1), s2.skip(1))
    } else {
        s1@[0] >= s2@[0]
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
/* code modified by LLM (iteration 5): Addressed compilation error by casting `j` to `int` when used with `s1.skip` and `s2.skip`. Also, fixed indexing `s1[j]` and `s2[j]` by using `@` for sequences. Corrected comparison operands for `len()` to be of type `nat` for `s1.len()` and `s2.len()`. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: nat = 0; // Changed to nat

    while i < x1.len()
        invariant
            result.len() == i,
            i <= x1.len(),
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result[j as usize] == string_lex_ge(x1[j as usize]@, x2[j as usize]@),
    {
        let s1 = x1[i as usize]@;
        let s2 = x2[i as usize]@;

        proof {
            if s1.len() == 0 {
                assert(string_lex_ge(s1, s2)) by { };
            } else if s2.len() == 0 {
                assert(string_lex_ge(s1, s2)) by { };
            } else if s1.len() > 0 && s2.len() > 0 && s1@[0] == s2@[0] {
                assert(string_lex_ge(s1, s2) == string_lex_ge(s1.skip(1), s2.skip(1))) by { };
            } else if s1.len() > 0 && s2.len() > 0 {
                assert(string_lex_ge(s1, s2) == (s1@[0] >= s2@[0])) by { };
            }
        }

        let mut current_ge = true;
        let mut j: nat = 0; // Changed to nat

        loop
            invariant
                j <= s1.len(),
                j <= s2.len(),
            decreases s1.len() + s2.len() - 2 * j as int,
        {
            if j >= s1.len() {
                current_ge = true;
                break;
            } else if j >= s2.len() {
                current_ge = true;
                break;
            } else if s1@[j] > s2@[j] {
                current_ge = true;
                break;
            } else if s1@[j] < s2@[j] {
                current_ge = false;
                break;
            } else {
                j = j + 1;
            }
        }
        result.push(current_ge);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}