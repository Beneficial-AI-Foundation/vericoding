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
/* helper modified by LLM (iteration 5): fixed string length access using ghost conversion */
proof fn lemma_clean_input_preserves_digits(s: Seq<char>)
    ensures
        forall|i: int| 0 <= i < clean_input(s).len() ==> (clean_input(s)[i] == '9' <==> exists|j: int| 0 <= j < s.len() && s[j] == '9' && clean_input(s)[i] == s[j])
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[s.len() - 1] == '\n' || s[s.len() - 1] == '\r' || s[s.len() - 1] == ' ' {
        lemma_clean_input_preserves_digits(s.subrange(0, (s.len() - 1) as int));
    }
}

proof fn lemma_contains_digit_nine_equiv(s: Seq<char>)
    ensures
        contains_digit_nine(s) <==> (exists|i: int| 0 <= i < s.len() && s[i] == '9')
{
}

fn check_for_digit_nine(s: &str) -> (found: bool)
    ensures
        found <==> contains_digit_nine(s@)
{
    let mut i = 0;
    let chars: Vec<char> = s.chars().collect();
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            chars@ == s@,
            !contains_digit_nine(s@.subrange(0, i as int))
    {
        if chars[i] == '9' {
            return true;
        }
        i += 1;
    }
    false
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
    /* code modified by LLM (iteration 5): fixed string length access using ghost conversion */
    let cleaned_equivalent = check_for_digit_nine(stdin_input);
    
    proof {
        lemma_clean_input_preserves_digits(stdin_input@);
        lemma_contains_digit_nine_equiv(clean_input(stdin_input@));
    }
    
    if cleaned_equivalent {
        "Yes\n".to_string()
    } else {
        "No\n".to_string()
    }
}
// </vc-code>


}

fn main() {}