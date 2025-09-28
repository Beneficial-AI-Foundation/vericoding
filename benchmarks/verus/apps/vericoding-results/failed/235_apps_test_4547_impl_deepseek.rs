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

proof fn lemma_contains_digit_nine_empty()
    ensures !contains_digit_nine(Seq::empty())
{
    assert forall|i: int| 0 <= i < 0 by { /* proof block for quantifier */ } implies false;
}

proof fn lemma_contains_digit_nine_push(s: Seq<char>, c: char)
    ensures contains_digit_nine(s.push(c)) == (contains_digit_nine(s) || c == '9')
{
    if c == '9' {
        assert(s.push(c)@[s.len()] == '9');
    } else {
        assert forall|i: int| 0 <= i < s.len() implies s.push(c)@[i] == s@[i] by { /* proof block */ };
        assert forall|i: int| i == s.len() implies s.push(c)@[i] == c by { /* proof block */ };
    }
}

proof fn lemma_clean_input_preserves_nine(s: Seq<char>)
    ensures contains_digit_nine(clean_input(s)) == contains_digit_nine(s)
    decreases s.len()
{
    if s.len() == 0 {
        lemma_contains_digit_nine_empty();
        assert(clean_input(s) == s);
    } else if s[s.len() - 1] == '\n' || s[s.len() - 1] == '\r' || s[s.len() - 1] == ' ' {
        lemma_clean_input_preserves_nine(s.subrange(0, s.len() - 1));
    } else {
        lemma_clean_input_preserves_nine(s.subrange(0, s.len() - 1));
        lemma_contains_digit_nine_push(s.subrange(0, s.len() - 1), s[s.len() - 1]);
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
    /* code modified by LLM (iteration 5): Add proof block and fix verification */
    proof {
        lemma_clean_input_preserves_nine(stdin_input@);
    }
    
    let cleaned_input = clean_input(stdin_input@);
    let mut found_nine = false;
    let mut i: usize = 0;
    while i < stdin_input.len()
        invariant
            i <= stdin_input@.len(),
            found_nine == contains_digit_nine(stdin_input@.subrange(0, i)),
        decreases stdin_input.len() - i
    {
        let ch = stdin_input.as_bytes()[i] as char;
        if ch == '9' {
            found_nine = true;
        }
        i += 1;
    }
    
    if found_nine {
        "Yes\n".to_string()
    } else {
        "No\n".to_string()
    }
}
// </vc-code>


}

fn main() {}