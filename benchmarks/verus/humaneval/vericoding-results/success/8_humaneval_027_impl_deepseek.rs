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

proof fn lemma_flip_char_properties()
    ensures
        forall|c: char| is_lowercase(c) ==> flip_char(c) == ((c as u8) - ('a' as u8) + ('A' as u8)) as char,
        forall|c: char| is_uppercase(c) ==> flip_char(c) == ((c as u8) - ('A' as u8) + ('a' as u8)) as char,
        forall|c: char| !is_lowercase(c) && !is_uppercase(c) ==> flip_char(c) == c
{
}

proof fn lemma_flip_case_correct(s: Seq<char>, result: Seq<char>)
    requires
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == flip_char(s[i])
    ensures
        valid_flip_case(s, result)
{
}

fn is_lowercase_exec(c: char) -> (b: bool)
    ensures b == is_lowercase(c)
{
    'a' <= c && c <= 'z'
}

fn is_uppercase_exec(c: char) -> (b: bool)
    ensures b == is_uppercase(c)
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
    /* code modified by LLM (iteration 2): Added executable helper functions and fixed compilation error */
    let mut result = Vec::<char>::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == flip_char(s@[j])
        decreases s.len() - i
    {
        let c = s[i];
        let flipped = if is_lowercase_exec(c) {
            ((c as u8) - ('a' as u8) + ('A' as u8)) as char
        } else if is_uppercase_exec(c) {
            ((c as u8) - ('A' as u8) + ('a' as u8)) as char
        } else {
            c
        };
        
        result.push(flipped);
        proof {
            lemma_flip_char_properties();
        }
        i += 1;
    }
    
    proof {
        lemma_flip_case_correct(s@, result@);
    }
    
    result
}
// </vc-code>


}

fn main() {}