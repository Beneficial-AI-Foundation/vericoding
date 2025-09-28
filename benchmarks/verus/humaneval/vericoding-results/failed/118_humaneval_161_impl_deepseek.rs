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

proof fn lemma_reverse_string_preserves_has_letter(s: Seq<char>)
    requires
        has_letter(s),
    ensures
        has_letter(reverse_string(s)),
{
    if s.len() > 0 {
        lemma_reverse_string_preserves_has_letter(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_reverse_string_no_letter(s: Seq<char>)
    requires
        !has_letter(s),
    ensures
        reverse_string(s) == s,
{
    if s.len() > 0 {
        lemma_reverse_string_no_letter(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_swap_case_involutive(c: char)
    ensures
        swap_case(swap_case(c)) == c,
{
    if 'A' <= c && c <= 'Z' {
        assert(swap_case(c) == ((c as u32 + 32) as char));
        assert(swap_case(swap_case(c)) == ((c as u32) as char));
    } else if 'a' <= c && c <= 'z' {
        assert(swap_case(c) == ((c as u32 - 32) as char));
        assert(swap_case(swap_case(c)) == ((c as u32) as char));
    } else {
        assert(swap_case(c) == c);
        assert(swap_case(swap_case(c)) == c);
    }
}

/* helper modified by LLM (iteration 5): Use char::from_u32 for proper char conversion */
spec fn swap_case_spec(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        char::from_u32(c as u32 + 32).unwrap()
    } else if 'a' <= c && c <= 'z' {
        char::from_u32(c as u32 - 32).unwrap()
    } else {
        c
    }
}

proof fn lemma_swap_case_equals_spec(c: char)
    ensures
        swap_case(c) == swap_case_spec(c),
{
}

proof fn lemma_swap_case_preserves_non_letters(c: char)
    requires
        !(('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')),
    ensures
        swap_case(c) == c,
{
}

proof fn lemma_reverse_string_length(s: Seq<char>)
    ensures
        reverse_string(s).len() == s.len(),
{
    if s.len() > 0 {
        lemma_reverse_string_length(s.subrange(0, s.len() as int - 1));
    }
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
    /* code modified by LLM (iteration 5): Replace char casting with char::from_u32 */
    if has_letter(s@) {
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                result@.len() == i as int,
                forall|j: int| 0 <= j < i ==> result@[j] == swap_case(s@[j]),
        {
            let c = s[i];
            let swapped = if 'A' <= c && c <= 'Z' {
                char::from_u32(c as u32 + 32).unwrap()
            } else if 'a' <= c && c <= 'z' {
                char::from_u32(c as u32 - 32).unwrap()
            } else {
                c
            };
            result.push(swapped);
            i = i + 1;
        }
        result
    } else {
        let mut i: usize = s.len();
        let mut result = Vec::new();
        while i > 0
            invariant
                0 <= i <= s.len(),
                result@.len() == (s.len() - i) as int,
                result@ == reverse_string(s@.subrange(i as int, s.len() as int)),
        {
            i = i - 1;
            result.push(s[i]);
        }
        result
    }
}
// </vc-code>


}

fn main() {}