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

// </vc-helpers>

// <vc-spec>
fn flip_case(s: Vec<char>) -> (result: Vec<char>)
    ensures valid_flip_case(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [brief description] */
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec@[j] == #[trigger] flip_char(#[trigger] s@[j]),

        decreases s.len() - i
    {
        let c = s[i];
        let flipped_c = if 'a' <= c && c <= 'z' { 
            ((c as u8) - ('a' as u8) + ('A' as u8)) as char
        } else if 'A' <= c && c <= 'Z' { 
            ((c as u8) - ('A' as u8) + ('a' as u8)) as char
        } else { 
            c 
        };
        result_vec.push(flipped_c);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}