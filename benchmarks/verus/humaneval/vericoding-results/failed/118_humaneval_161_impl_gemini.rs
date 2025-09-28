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
proof fn lemma_reverse_len(s: Seq<char>)
    ensures reverse_string(s).len() == s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_reverse_len(s.subrange(0, s.len() as int - 1));
    }
}

/* helper modified by LLM (iteration 3): fixed Seq indexing syntax and strengthened proof */
proof fn lemma_reverse_index(s: Seq<char>)
    ensures
        forall|j: int| 0 <= j < s.len() ==> reverse_string(s)[j] == s[s.len() - 1 - j],
    decreases s.len()
{
    if s.len() > 0 {
        let s_short = s.subrange(0, s.len() as int - 1);
        lemma_reverse_index(s_short);
        assert forall|j: int| 0 <= j < s.len() implies reverse_string(s)[j] == s[s.len() - 1 - j] by {
            if j == 0 {
                assert(reverse_string(s)[0] == s[s.len() - 1]);
            } else {
                assert(reverse_string(s)[j] == reverse_string(s_short)[j - 1]);
                assert(reverse_string(s_short)[j - 1] == s_short[s_short.len() - 1 - (j-1)]);
                assert(s_short[s_short.len() - 1 - (j-1)] == s[s.len() - 1 - j]);
            }
        }
    }
}

/* helper modified by LLM (iteration 5): added decreases clause to loop */
fn has_letter_exec(s: &Vec<char>) -> (result: bool)
    requires s.len() < usize::MAX,
    ensures result == has_letter(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            !has_letter(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let c = s[i];
        if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') {
            return true;
        }
        i = i + 1;
    }
    return false;
}

/* helper modified by LLM (iteration 5): added decreases clause to loop */
fn swap_case_vector(s: &Vec<char>) -> (result: Vec<char>)
    requires s.len() < usize::MAX,
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == swap_case(s@[i]),
{
    let mut result = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            s.len() < usize::MAX,
            0 <= i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == swap_case(s@[j]),
        decreases s.len() - i
    {
        let c = s[i];
        let swapped_c = if 'A' <= c && c <= 'Z' {
            (c as u8 + 32) as char
        } else if 'a' <= c && c <= 'z' {
            (c as u8 - 32) as char
        } else {
            c
        };
        result.push(swapped_c);
        i = i + 1;
    }
    result
}

/* helper modified by LLM (iteration 5): added decreases clause to loop */
fn reverse_vector(s: &Vec<char>) -> (result: Vec<char>)
    requires s.len() < usize::MAX,
    ensures
        result@.len() == s@.len(),
        result@ == reverse_string(s@),
{
    let mut result = Vec::with_capacity(s.len());
    let len = s.len();
    let mut i: usize = 0;
    while i < len
        invariant
            s.len() < usize::MAX,
            len == s.len(),
            0 <= i <= len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[len - 1 - j],
        decreases len - i
    {
        result.push(s[len - 1 - i]);
        i = i + 1;
    }
    proof {
        lemma_reverse_len(s@);
        lemma_reverse_index(s@);
        assert(result@ == reverse_string(s@));
    }
    result
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
    /* code modified by LLM (iteration 5): logic correctly delegates to helpers, no changes needed */
    let has_l = has_letter_exec(&s);
    if has_l {
        swap_case_vector(&s)
    } else {
        reverse_vector(&s)
    }
}
// </vc-code>


}

fn main() {}