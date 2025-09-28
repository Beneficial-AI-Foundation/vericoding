// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed erroneous 'as nat' cast for Seq indexing */
proof fn lemma_spec_equivalence(s: Seq<char>)
    ensures
        (exists|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2) <==>
        (s.len() >= 3 && s[s.len() - 3] == '.'),
{
    if exists|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2 {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2;
        assert(i == s.len() - 3);
        assert(s.len() >= 3 && s[s.len() - 3] == '.');
    }
    if s.len() >= 3 && s[s.len() - 3] == '.' {
        let i = s.len() - 3;
        assert(exists|j: int| j == i && 0 <= j < s.len() && s[j] == '.' && s.len() - j - 1 == 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified logic using char iterators and short-circuiting */
    let char_count = s.chars().count();
    let result = char_count >= 3 && s.chars().nth(char_count - 3) == Some('.');

    proof {
        lemma_spec_equivalence(s@);
    }

    result
}
// </vc-code>

}
fn main() {}