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
/* helper modified by LLM (iteration 5): Removed helper, it was not needed. */
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
/* code modified by LLM (iteration 5): Added `let current_len` inside the invariant block to fix scope error. */
{
    let mut result: Vec<char> = Vec::new();
    if s.len() > 0 && exists|i: int| 0 <= i < s.len() && (('A' <= s@[i] && s@[i] <= 'Z') || ('a' <= s@[i] && s@[i] <= 'z')) {
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i,
                i <= s.len(),
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == swap_case(s@[j]),
            decreases s.len() - i
        {
            result.push(swap_case(s[i]));
            i = i + 1;
        }
    } else {
        let mut i: usize = s.len();
        while i > 0
            invariant
                0 <= i,
                i <= s.len(),
                result@.len() == s.len() - i,
                forall|j: int| 0 <= j < s.len() - i ==> result@[j] == s@[s.len() - ((s.len() - i) as int) + j as int],
                ({ let current_len: nat = (s.len() - i) as nat; (result@) == reverse_string(s@.subrange(i as int, s@.len() as int)) }),
            decreases i
        {
            i = i - 1;
            result.push(s[i]);
        }
        proof {
            assert(reverse_string(s@) == result@);
        }
    }
    result
}
// </vc-code>


}

fn main() {}