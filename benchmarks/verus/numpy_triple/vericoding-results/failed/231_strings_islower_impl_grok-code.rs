// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added exec versions of is_alpha_char and is_lower_char with ensures to match spec. */
fn is_alpha_char_exec(c: char) -> (result: bool)
    ensures
        result == is_alpha_char(c)
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

fn is_lower_char_exec(c: char) -> (result: bool)
    ensures
        result == is_lower_char(c)
{
    'a' <= c && c <= 'z'
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

spec fn is_lower_char(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn string_has_cased_char(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn string_all_cased_are_lowercase(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_lower_char(s[i])
}

fn islower(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i as int] == (string_has_cased_char(a[i]@) && string_all_cased_are_lowercase(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch in proof block by casting i to int for Vec indexing with @. */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i as int,
            forall|k: int| 0 <= k < i ==> result[k] == (string_has_cased_char(a[k]@) && string_all_cased_are_lowercase(a[k]@))
    {
        let s = &a[i];
        let s_vec: Vec<char> = s.chars().collect();
        proof { assert(s_vec@ == a[i as int]@); }
        let mut has_cased = false;
        let mut all_lower_if_cased = true;
        let mut j = 0;
        while j < s_vec.len()
            invariant
                has_cased == exists|m: int| 0 <= m < j && is_alpha_char(s_vec@[m]),
                all_lower_if_cased == forall|m: int| 0 <= m < j && is_alpha_char(s_vec@[m]) ==> is_lower_char(s_vec@[m])
        {
            if is_alpha_char_exec(s_vec[j]) {
                has_cased = true;
                if !is_lower_char_exec(s_vec[j]) {
                    all_lower_if_cased = false;
                }
            }
            j += 1;
        }
        result.push(has_cased && all_lower_if_cased);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}