// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn exec_is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

proof fn exec_is_alpha_char_equiv(c: char)
    ensures
        exec_is_alpha_char(c) == is_alpha_char(c)
{
    assert(exec_is_alpha_char(c) == is_alpha_char(c));
}

/* helper modified by LLM (iteration 5): replaced s.is_empty() with s@.len() == 0 to fix compilation error */
fn check_string(s: &String) -> (b: bool)
    ensures
        b == string_is_alpha(s@)
{
    if s@.len() == 0 {
        false
    } else {
        let chars = s.chars().collect::<Vec<char>>();
        let n = chars.len();
        let mut i = 0;
        let mut all_alpha = true;
        while i < n
            invariant
                0 <= i <= n,
                all_alpha == (forall|j: int| 0 <= j < i ==> is_alpha_char(chars@[j])),
        {
            let c = chars[i];
            let is_alpha = exec_is_alpha_char(c);
            proof {
                exec_is_alpha_char_equiv(c);
            }
            if !is_alpha {
                all_alpha = false;
            }
            i += 1;
        }
        all_alpha
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
    /* code modified by LLM (iteration 5): updated to use fixed check_string helper */
    let mut result = Vec::new();
    let mut i = 0;
    let n = input.len();
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_is_alpha(input[j]@),
    {
        let s = &input[i];
        let b = check_string(s);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}