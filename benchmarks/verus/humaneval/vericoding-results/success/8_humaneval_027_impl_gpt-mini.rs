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
/* helper modified by LLM (iteration 4): execution version of flip_char with postcondition */
fn flip_char_exec(c: char) -> (result: char)
    ensures
        flip_char(c) == result,
{
    if 'a' <= c && c <= 'z' {
        (((c as u8) - ('a' as u8) + ('A' as u8)) as char)
    } else if 'A' <= c && c <= 'Z' {
        (((c as u8) - ('A' as u8) + ('a' as u8)) as char)
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn flip_case(s: Vec<char>) -> (result: Vec<char>)
    ensures valid_flip_case(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use runtime flip_char_exec and maintain invariant */
    let mut i: usize = 0;
    let mut res: Vec<char> = Vec::new();
    while i < s.len()
        invariant
            0usize <= i <= s.len(),
            res@.len() == (i as int),
            forall|j: int| 0 <= j < res@.len() ==> res@[j] == flip_char(s@[j]),
        decreases s.len() - i
    {
        let c: char = s[i];
        let f: char = flip_char_exec(c);
        res.push(f);
        proof {
            assert(res@.len() == (i as int) + 1);
            assert(res@[i as int] == f);
            assert(flip_char(s@[i as int]) == f);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}