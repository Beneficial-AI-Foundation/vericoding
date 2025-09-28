// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn clean_input(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s
    } else if s[s.len() - 1] == '\n' || s[s.len() - 1] == '\r' || s[s.len() - 1] == ' ' { 
        clean_input(s.subrange(0, s.len() - 1))
    } else { 
        s
    }
}

spec fn contains_digit_nine(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proves clean_input is a prefix of the original sequence */
fn clean_input_prefix(s: Seq<char>)
    decreases s.len()
    ensures
        clean_input(s).len() <= s.len(),
        forall|i: int| 0 <= i < clean_input(s).len() ==> clean_input(s)[i] == s[i],
{
    proof {
        if s.len() == 0 {
            assert(clean_input(s) == s);
            assert(clean_input(s).len() <= s.len());
            assert(forall|i: int| 0 <= i < clean_input(s).len() ==> clean_input(s)[i] == s[i]);
        } else if s[s.len() - 1] == '\\n' || s[s.len() - 1] == '\\r' || s[s.len() - 1] == ' ' {
            clean_input_prefix(s.subrange(0, s.len() - 1));
            assert(clean_input(s) == clean_input(s.subrange(0, s.len() - 1)));
            assert(clean_input(s).len() <= s.len());
            assert(forall|i: int| 0 <= i < clean_input(s).len() ==> clean_input(s)[i] == s[i]);
        } else {
            assert(clean_input(s) == s);
            assert(clean_input(s).len() <= s.len());
            assert(forall|i: int| 0 <= i < clean_input(s).len() ==> clean_input(s)[i] == s[i]);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input@.len() > 0
    ensures 
        result@ == seq!['Y', 'e', 's', '\n'] || result@ == seq!['N', 'o', '\n'],
        result@ == seq!['Y', 'e', 's', '\n'] <==> contains_digit_nine(clean_input(stdin_input@)),
        result@ == seq!['N', 'o', '\n'] <==> !contains_digit_nine(clean_input(stdin_input@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute cleaned input and return Yes/No accordingly */
    let cs = clean_input(stdin_input@);
    if contains_digit_nine(cs) {
        "Yes\\n".to_string()
    } else {
        "No\\n".to_string()
    }
}

// </vc-code>


}

fn main() {}