// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that string_is_alpha implies char at index is alpha */
proof fn lemma_string_is_alpha_index(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        string_is_alpha(s),
{
    proof {
        assert(string_is_alpha(s));
        assert(forall|k: int| 0 <= k < s.len() ==> is_alpha_char(s[k]));
        assert(is_alpha_char(s[i]));
    }
}

// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn string_is_alpha(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_alpha_char(s[i])
}

fn is_alpha(input: Vec<String>) -> (ret: Vec<bool>)
    ensures
        ret.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            ret[i] == string_is_alpha(input[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over input Vec and compute string_is_alpha for each String */
    let mut ret: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            ret.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> ret@[j] == string_is_alpha(input@[j]@),
        decreases input.len() - i
    {
        let s = input[i].clone();
        let b = string_is_alpha(s@);
        ret.push(b);
        i = i + 1;
    }
    ret
}

// </vc-code>


}
fn main() {}