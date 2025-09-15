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
/* helper modified by LLM (iteration 5): Fixed filter function signature to match expected tuple format */
spec fn filtered_lower_seq(s: Seq<char>) -> Seq<char> {
    s.filter(|c| is_alphanumeric(c)).map(|c| to_lowercase(c))
}

proof fn seq_reverse_property<T>(s: Seq<T>) 
    ensures 
        s.reverse().reverse() == s
{
    if s.len() > 0 {
        let first = s[0];
        let rest = s.subrange(1, s.len() as int);
        seq_reverse_property(rest);
    }
}

proof fn palindrome_property(seq: Seq<char>) 
    ensures 
        seq == seq.reverse() ==> (
            forall|i: int, j: int| 0 <= i < seq.len() && 0 <= j < seq.len() ==> seq[i] == seq[j] ==> i == j || seq[i] == seq[j]
        )
{
    if seq.len() > 0 {
        let first = seq[0];
        let last = seq[seq.len() - 1];
        let middle = seq.subrange(1, (seq.len() - 1) as int);
        if first == last {
            palindrome_property(middle);
        }
    }
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
/* code modified by LLM (iteration 5): Fixed Vec indexing and subrange parameters */
{
    let mut cleaned: Vec<char> = Vec::new();
    let mut iter = s.chars();
    let mut count = 0;
    
    while let Some(c) = iter.next()
        invariant 
            count == iter.count(),
            cleaned@ == filtered_lower_seq(s@.subrange(0, count as int))
    {
        if is_alphanumeric(c) {
            cleaned.push(to_lowercase(c));
        }
        count = count + 1;
    }
    
    let mut left: usize = 0;
    let mut right = cleaned.len() - 1;
    let mut result: bool = true;
    
    while left < right
        invariant 
            0 <= left <= right < cleaned.len(),
            result ==> (
                forall|i: int| 0 <= i < left ==> forall|j: int| right < j < cleaned.len() ==> cleaned@[i] == cleaned@[j] ==> i == j || cleaned@[i] == cleaned@[j]
            )
    {
        if cleaned[left] != cleaned[right] {
            result = false;
            break;
        }
        left = left + 1;
        right = right - 1;
    }
    
    proof {
        let forward_seq = cleaned@;
        let backward_seq = forward_seq.reverse();
        if result {
            palindrome_property(forward_seq);
        }
        seq_reverse_property(cleaned@);
    }
    
    result
}
// </vc-code>

}
fn main() {}