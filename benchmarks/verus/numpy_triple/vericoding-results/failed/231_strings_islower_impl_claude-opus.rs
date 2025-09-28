// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Using String iterator to avoid nat/int type issues */
fn check_islower(s: &String) -> (result: bool)
    ensures
        result == (string_has_cased_char(s@) && string_all_cased_are_lowercase(s@))
{
    let mut has_cased = false;
    let mut all_lower = true;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_cased == exists|j: int| 0 <= j < i && is_alpha_char(s@[j]),
            all_lower == forall|j: int| 0 <= j < i && is_alpha_char(s@[j]) ==> is_lower_char(s@[j])
    {
        let c = s.get_char(i);
        if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') {
            has_cased = true;
            if !(c >= 'a' && c <= 'z') {
                all_lower = false;
            }
        }
        i = i + 1;
    }
    
    has_cased && all_lower
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
    /* code modified by LLM (iteration 5): Using usize consistently to avoid nat/int issues */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (string_has_cased_char(a[j]@) && string_all_cased_are_lowercase(a[j]@))
    {
        let checked = check_islower(&a[i]);
        result.push(checked);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}