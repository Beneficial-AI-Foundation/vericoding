// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use usize for loop counter to fix type error */
fn char_is_whitespace(c: char) -> (result: bool)
    ensures result == is_whitespace_char(c)
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

fn string_all_whitespace(s: &str) -> (result: bool)
    ensures result == (s@.len() > 0 && all_chars_whitespace(s@))
{
    let chars = s@;
    if chars.len() == 0 {
        false
    } else {
        let mut i: usize = 0;
        let mut all_white = true;
        while i < chars.len()
            invariant
                0 <= i <= chars.len(),
                all_white == forall|j: int| 0 <= j < i as int ==> is_whitespace_char(chars[j as int]),
        {
            let c = chars[i as int];
            if !char_is_whitespace(c) {
                all_white = false;
                break;
            }
            i = i + 1;
        }
        proof {
            if all_white {
                assert(i == chars.len());
                assert(forall|j: int| 0 <= j < chars.len() ==> is_whitespace_char(chars[j]));
                assert(all_chars_whitespace(chars));
            }
        }
        all_white
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_whitespace_char(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

spec fn all_chars_whitespace(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_whitespace_char(s[0]) && all_chars_whitespace(s.skip(1))
    }
}

fn isspace(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_whitespace(a[i]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i]@.len() == 0 ==> result[i] == false),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implementation unchanged */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < i ==> (a[j]@.len() == 0 ==> result[j] == false),
    {
        let s: &str = a[i].as_str();
        let is_all_space = string_all_whitespace(s);
        result.push(is_all_space);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}