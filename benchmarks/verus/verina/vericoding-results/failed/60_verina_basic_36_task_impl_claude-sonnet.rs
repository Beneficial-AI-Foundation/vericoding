// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented manual character processing without using unsupported collect() */
fn char_replace(s: &str) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==>
            #[trigger] result@.index(i) ==
            if is_space_comma_dot(#[trigger] s@.index(i)) { ':' } else { s@.index(i) },
{
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==>
                #[trigger] result@.index(j) ==
                if is_space_comma_dot(#[trigger] s@.index(j)) { ':' } else { s@.index(j) },
    {
        let c = s@.index(i as int);
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}

fn vec_char_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result@.len() == chars@.len(),
        forall|i: int| 0 <= i < chars@.len() ==> result@.index(i) == chars@.index(i),
{
    let mut result = String::new();
    let mut i = 0;
    while i < chars.len()
        invariant
            0 <= i <= chars@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@.index(j) == chars@.index(j),
    {
        result.push(chars[i]);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            #[trigger] result@.index(i) == 
            if is_space_comma_dot(#[trigger] s@.index(i)) { ':' } else { s@.index(i) },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper functions to avoid unsupported collect() */
    let char_vec = char_replace(s);
    let result = vec_char_to_string(char_vec);
    result
}
// </vc-code>

}
fn main() {}