// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_alphanumeric(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

spec fn to_lowercase(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u32) + 32) as char
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn clean_and_lowercase(s: Seq<char>) -> Seq<char> {
    s.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c))
}

lemma lemma_palindrome_check(cleaned: Seq<char>)
    ensures cleaned == cleaned.reverse() <==> (
        forall|i: int| 0 <= i < cleaned.len() ==> cleaned[i] == cleaned[cleaned.len() - 1 - i]
    )
{
}

fn is_palindrome_cleaned(cleaned: &Vec<char>) -> (result: bool)
    requires cleaned@.len() >= 0
    ensures result <==> cleaned@ == cleaned@.reverse()
{
    let len = cleaned.len();
    let mut i = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> cleaned@[j] == cleaned@[len - 1 - j],
    {
        if cleaned[i] != cleaned[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    
    proof {
        lemma_palindrome_check(cleaned@);
    }
    
    true
}
// </vc-helpers>

// <vc-spec>
fn palindrome_ignore_non_alnum(s: &str) -> (result: bool)
    ensures 
        result <==> ({
            let chars_seq = s@;
            let cleaned = chars_seq.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c));
            let forward = cleaned;
            let backward = cleaned.reverse();
            forward == backward
        })
// </vc-spec>
// <vc-code>
{
    let chars_seq = s@;
    let mut cleaned = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            cleaned@ == chars_seq.subrange(0, i as int).filter(|c: char| is_alphanumeric(c)).map(|j, c: char| to_lowercase(c)),
    {
        let c = s.as_bytes()[i] as char;
        if is_alphanumeric(c) {
            let lower_c = if 'A' <= c && c <= 'Z' {
                ((c as u32) + 32) as char
            } else {
                c
            };
            cleaned.push(lower_c);
        }
        i += 1;
    }
    
    let result = is_palindrome_cleaned(&cleaned);
    
    proof {
        let expected_cleaned = clean_and_lowercase(chars_seq);
        assert(cleaned@ == expected_cleaned);
    }
    
    result
}
// </vc-code>

}
fn main() {}