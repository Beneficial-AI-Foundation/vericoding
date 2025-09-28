// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added forall/recursion equivalence lemma */
proof fn lemma_all_chars_alpha_is_forall(s: Seq<char>)
    ensures all_chars_alpha(s) <==> (forall |k: int| 0 <= k < s.len() ==> is_alpha_char(s[k]))
    decreases s.len()
{
    if s.len() > 0 {
        lemma_all_chars_alpha_is_forall(s.skip(1));
    }
}

/* helper modified by LLM (iteration 5): fixed compilation error by using s@.len() for string length */
fn string_is_alpha(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_alpha(s@)),
{
    if s@.len() == 0 {
        return false;
    }

    let mut i: usize = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            forall|j: int| 0 <= j < i as int ==> is_alpha_char(s@[j]),
        decreases (s@.len() as int) - (i as int)
    {
        let c = s.get_char(i);
        if !('a' <= c && c <= 'z') && !('A' <= c && c <= 'Z') {
            proof { lemma_all_chars_alpha_is_forall(s@); }
            return false;
        }
        i = i + 1;
    }
    
    proof { lemma_all_chars_alpha_is_forall(s@); }
    return true;
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
/* code modified by LLM (iteration 5): updated comment, no logic change */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alpha(a[j]@)),
        decreases a.len() - i
    {
        let s_ref = &a[i];
        let is_a = string_is_alpha(s_ref);
        result.push(is_a);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}