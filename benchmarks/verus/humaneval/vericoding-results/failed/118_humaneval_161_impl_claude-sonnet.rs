// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_letter(s: Seq<char>) -> bool
{
    exists|i: int| 0 <= i < s.len() && (('A' <= s[i] && s[i] <= 'Z') || ('a' <= s[i] && s[i] <= 'z'))
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s 
    } else { 
        s.subrange(s.len() as int - 1, s.len() as int).add(reverse_string(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn swap_case(c: char) -> char
{
    if 'A' <= c && c <= 'Z' { 
        ((c as u32 + 32) as char)
    } else if 'a' <= c && c <= 'z' { 
        ((c as u32 - 32) as char)
    } else { 
        c 
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn swap_case_seq(s: Seq<char>) -> Seq<char>
{
    s.map(|i: int, c: char| swap_case(c))
}

/* helper modified by LLM (iteration 5): fixed ensures clauses to use return value directly */
fn char_to_lower(c: char) -> (result: char)
    requires 'A' <= c && c <= 'Z'
    ensures result == ((c as u32 + 32) as char)
{
    char::from_u32(c as u32 + 32).unwrap()
}

fn char_to_upper(c: char) -> (result: char)
    requires 'a' <= c && c <= 'z'
    ensures result == ((c as u32 - 32) as char)
{
    char::from_u32(c as u32 - 32).unwrap()
}

proof fn reverse_string_len(s: Seq<char>)
    ensures reverse_string(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        reverse_string_len(s.subrange(0, s.len() as int - 1));
    }
}

proof fn swap_case_seq_len(s: Seq<char>)
    ensures swap_case_seq(s).len() == s.len()
{
}

proof fn swap_case_seq_index(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures swap_case_seq(s)[i] == swap_case(s[i])
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures (if has_letter(s@) {
        result@.len() == s@.len() && 
        (forall|i: int| 0 <= i < s@.len() ==> result@[i] == swap_case(s@[i]))
    } else {
        result@ == reverse_string(s@)
    }) && result@.len() == s@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed helper function calls to match corrected signatures */
    let mut result = Vec::new();
    let mut has_letter_found = false;
    
    let mut j = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            has_letter_found == exists|k: int| 0 <= k < j && (('A' <= s@[k] && s@[k] <= 'Z') || ('a' <= s@[k] && s@[k] <= 'z')),
    {
        let c = s[j];
        if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') {
            has_letter_found = true;
        }
        j += 1;
    }
    
    if has_letter_found {
        let mut i = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result@[k] == swap_case(s@[k]),
        {
            let c = s[i];
            let swapped = if 'A' <= c && c <= 'Z' {
                char_to_lower(c)
            } else if 'a' <= c && c <= 'z' {
                char_to_upper(c)
            } else {
                c
            };
            result.push(swapped);
            i += 1;
        }
        proof {
            swap_case_seq_len(s@);
        }
    } else {
        let mut i = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result@[k] == s@[s.len() - 1 - k],
        {
            result.push(s[s.len() - 1 - i]);
            i += 1;
        }
        proof {
            reverse_string_len(s@);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}