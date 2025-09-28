// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn exec_is_alpha_char(c: char) -> (res: bool)
    ensures
        res == is_alpha_char(c),
{
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

/* helper modified by LLM (iteration 5): [fixed compilation error by replacing ext_equal with == and adding proof] */
fn check_string_is_alpha(s: &String) -> (ret: bool)
    ensures
        ret == string_is_alpha(s@),
{
    let chars: Vec<char> = s.chars().collect();
    proof {
        vstd::string::lemma_string_view_is_chars(s);
    }

    if chars.len() == 0 {
        return false;
    }

    let mut i: usize = 0;
    while i < chars.len()
        invariant
            s@ == chars@,
            0 <= i <= chars.len(),
            forall|j: int| 0 <= j < i as int ==> is_alpha_char(s@[j]),
    {
        let c = chars[i];
        if !exec_is_alpha_char(c) {
            return false;
        }
        i = i + 1;
    }
    
    true
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
    /* code modified by LLM (iteration 5): [no changes; logic is correct with fixed helper] */
    let mut ret: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i as int ==> ret@[j] == string_is_alpha(input@[j]@),
    {
        let s = &input[i];
        let is_a = check_string_is_alpha(s);
        ret.push(is_a);
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}