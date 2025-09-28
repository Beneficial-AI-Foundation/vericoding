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
/* helper modified by LLM (iteration 2): fixed result variable in ensures clause */
fn is_letter(c: char) -> (result: bool)
    ensures result == (('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z'))
{
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

fn swap_case_char(c: char) -> (result: char)
    ensures result == swap_case(c)
{
    if 'A' <= c && c <= 'Z' {
        ((c as u32 + 32) as char)
    } else if 'a' <= c && c <= 'z' {
        ((c as u32 - 32) as char)
    } else {
        c
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
/* code modified by LLM (iteration 2): fixed int type usage in loop by using usize */
{
    let mut has_letter = false;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_letter ==> exists|j: int| 0 <= j < i && is_letter(s@[j]),
            !has_letter ==> forall|j: int| 0 <= j < i ==> !is_letter(s@[j]),
        decreases s.len() - i
    {
        if is_letter(s[i]) {
            has_letter = true;
            break;
        }
        i += 1;
    }
    
    if has_letter {
        let mut result = Vec::new();
        let mut i = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                forall|j: int| 0 <= j < i ==> result@[j] == swap_case(s@[j]),
            decreases s.len() - i
        {
            result.push(swap_case_char(s[i]));
            i += 1;
        }
        result
    } else {
        let mut result = Vec::new();
        let mut i = s.len();
        while i > 0
            invariant
                0 <= i <= s.len(),
                forall|j: int| 0 <= j < (s@.len() - i as int) ==> result@[j] == s@[s@.len() - 1 - j],
            decreases i
        {
            i -= 1;
            result.push(s[i]);
        }
        proof {
            assert(result@ == reverse_string(s@));
        }
        result
    }
}
// </vc-code>


}

fn main() {}