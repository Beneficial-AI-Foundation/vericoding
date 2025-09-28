// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_alpha_char_exec(c: char) -> (result: bool)
    ensures result == is_alpha_char(c)
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

/* helper modified by LLM (iteration 5): fixed compilation by avoiding collect and using for-loop over chars */
fn all_chars_alpha_exec(s: &str) -> (result: bool)
    ensures result == (s@.len() > 0 && all_chars_alpha(s@))
{
    if s.is_empty() {
        false
    } else {
        let mut all_alpha = true;
        for c in s.chars() {
            if !is_alpha_char_exec(c) {
                all_alpha = false;
                break;
            }
        }
        all_alpha
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alpha_char(s[0]) && all_chars_alpha(s.skip(1))
    }
}

fn isalpha(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() == 0 ==> result[i as int] == false),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() > 0 ==> (result[i as int] <==> all_chars_alpha(a[i as int]@))),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> a[i as int]@.len() > 0),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> all_chars_alpha(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using fixed helper function with for-loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alpha(a[j]@)),
        decreases a.len() - i
    {
        let s = a[i];
        result.push(all_chars_alpha_exec(&s));
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}