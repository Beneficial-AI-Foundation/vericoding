// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lowercase(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn is_uppercase(c: char) -> bool {
    'A' <= c <= 'Z'
}

spec fn flip_char(c: char) -> char {
    if is_lowercase(c) { 
        ((c as u8) - ('a' as u8) + ('A' as u8)) as char
    } else if is_uppercase(c) { 
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else { 
        c 
    }
}

spec fn valid_flip_case(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() &&
    forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == #[trigger] flip_char( #[trigger] s[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed syntax for proof lemmas */
proof fn flip_char_properties(c: char)
    ensures
        is_lowercase(c) ==> is_uppercase(flip_char(c)),
        is_uppercase(c) ==> is_lowercase(flip_char(c)),
        !is_lowercase(c) && !is_uppercase(c) ==> flip_char(c) == c
{
}

proof fn flip_char_correct(c: char)
    ensures
        flip_char(c) == if is_lowercase(c) {
            ((c as u8) - ('a' as u8) + ('A' as u8)) as char
        } else if is_uppercase(c) {
            ((c as u8) - ('A' as u8) + ('a' as u8)) as char
        } else {
            c
        }
{
}

fn exec_is_lowercase(c: char) -> (result: bool)
    ensures result == is_lowercase(c)
{
    'a' <= c && c <= 'z'
}

fn exec_is_uppercase(c: char) -> (result: bool)
    ensures result == is_uppercase(c)
{
    'A' <= c && c <= 'Z'
}
// </vc-helpers>

// <vc-spec>
fn flip_case(s: Vec<char>) -> (result: Vec<char>)
    ensures valid_flip_case(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Used executable helper functions instead of spec functions */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == #[trigger] flip_char(#[trigger] s@[j])
        decreases s.len() - i
    {
        let c = s[i];
        let flipped = if exec_is_lowercase(c) {
            ((c as u8) - ('a' as u8) + ('A' as u8)) as char
        } else if exec_is_uppercase(c) {
            ((c as u8) - ('A' as u8) + ('a' as u8)) as char
        } else {
            c
        };
        
        proof {
            flip_char_correct(c);
        }
        
        result.push(flipped);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}