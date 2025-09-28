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
/* helper modified by LLM (iteration 5): Added helper to prove clean_input preserves digit nine */
proof fn clean_input_maintains_nine(s: Seq<char>)
    ensures
        contains_digit_nine(clean_input(s)) <==> contains_digit_nine(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[s.len() - 1] == '\n' || s[s.len() - 1] == '\r' || s[s.len() - 1] == ' ' {
        assert(clean_input(s) == clean_input(s.subrange(0, s.len() - 1)));
        assert(forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == s.subrange(0, s.len() - 1)[i]);
        clean_input_maintains_nine(s.subrange(0, s.len() - 1));
    } else {
        assert(clean_input(s) == s);
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
    /* code modified by LLM (iteration 5): Use index-based loop instead of iterator */
    let mut found_nine = false;
    let mut i: usize = 0;
    
    while i < stdin_input@.len()
        invariant
            0 <= i <= stdin_input@.len(),
            found_nine <==> exists|j: int| 0 <= j < i && stdin_input@[j] == '9',
    {
        if stdin_input@[i] == '9' {
            found_nine = true;
            assert(stdin_input@[i as int] == '9');
            assert(exists|j: int| 0 <= j < stdin_input@.len() && stdin_input@[j] == '9');
            break;
        }
        i = i + 1;
    }
    
    proof {
        clean_input_maintains_nine(stdin_input@);
        if found_nine {
            assert(contains_digit_nine(stdin_input@));
            assert(contains_digit_nine(clean_input(stdin_input@)));
        } else {
            assert(forall|j: int| 0 <= j < stdin_input@.len() ==> stdin_input@[j] != '9');
            assert(!contains_digit_nine(stdin_input@));
            assert(!contains_digit_nine(clean_input(stdin_input@)));
        }
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