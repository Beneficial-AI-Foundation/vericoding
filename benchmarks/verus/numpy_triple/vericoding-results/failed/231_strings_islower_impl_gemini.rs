// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed compilation error by removing call to non-existent lemma.] */
fn check_string_properties(s: &String) -> (result: bool)
    ensures
        result == (string_has_cased_char(s@) && string_all_cased_are_lowercase(s@)),
{
    let s_vec: Vec<char> = s.chars().collect();

    let mut has_cased_char = false;
    let mut all_cased_are_lowercase = true;
    let mut i: usize = 0;
    
    while i < s_vec.len()
        invariant
            0 <= i <= s_vec.len(),
            s_vec@ == s@,
            has_cased_char == string_has_cased_char(s_vec@.subrange(0, i as int)),
            all_cased_are_lowercase == string_all_cased_are_lowercase(s_vec@.subrange(0, i as int)),
        decreases s_vec.len() - i
    {
        let c = s_vec[i];
        if is_alpha_char(c) {
            has_cased_char = true;
            if !is_lower_char(c) {
                all_cased_are_lowercase = false;
            }
        }
        i = i + 1;
    }
    
    has_cased_char && all_cased_are_lowercase
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
    /* code modified by LLM (iteration 5): [No changes as the logic seems correct; fixed helper.] */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                result[j] == (string_has_cased_char(a[j]@) && string_all_cased_are_lowercase(a[j]@)),
        decreases a.len() - i
    {
        let b = check_string_properties(&a[i]);
        result.push(b);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}