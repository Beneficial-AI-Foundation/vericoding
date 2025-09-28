// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix numeric literal by using 0 instead of 0nat */
fn check_string_alpha(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_alpha(s@))
{
    if s@.len() == 0 {
        return false;
    }
    
    let chars_vec: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars_vec.len()
        invariant
            0 <= i <= chars_vec.len(),
            chars_vec.len() == s@.len(),
            chars_vec@ == s@,
            forall|j: int| 0 <= j < i ==> is_alpha_char(s@[j])
    {
        let c = chars_vec[i];
        if !((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < s@.len() ==> is_alpha_char(s@[j]));
        lemma_all_chars_alpha_complete(s@);
    }
    
    true
}

proof fn lemma_all_chars_alpha_complete(s: Seq<char>)
    requires
        forall|j: int| 0 <= j < s.len() ==> is_alpha_char(s[j])
    ensures
        all_chars_alpha(s)
    decreases s.len()
{
    if s.len() == 0 {
        return;
    }
    lemma_all_chars_alpha_complete(s.skip(1));
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
    /* code modified by LLM (iteration 5): main implementation using helper */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alpha(a[j]@))
    {
        let is_alpha = check_string_alpha(&a[i]);
        result.push(is_alpha);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}