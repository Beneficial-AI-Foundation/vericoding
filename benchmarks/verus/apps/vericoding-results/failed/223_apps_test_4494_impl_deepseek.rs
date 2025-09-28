// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 
    ({
        let s = if input[input.len()-1] == '\n' { 
            input.subrange(0, input.len() - 1)
        } else { 
            input
        };
        s == "ABC"@ || s == "ARC"@
    })
}

spec fn normalize_input(input: Seq<char>) -> Seq<char>
    recommends input.len() > 0
{
    if input[input.len()-1] == '\n' { 
        input.subrange(0, input.len() - 1)
    } else { 
        input
    }
}

spec fn expected_output(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let s = normalize_input(input);
    if s == "ABC"@ { "ARC\n"@ } else { "ABC\n"@ }
}
// </vc-preamble>

// <vc-helpers>
fn normalize_input_impl(input: String) -> (normalized: String)
    requires 
        input@.len() > 0,
    ensures 
        normalized@ == normalize_input(input@)
{
    /* helper modified by LLM (iteration 5): avoid complex &mut arguments by using chars().count() */
    proof {
        let s = input@;
        if s[s.len()-1] == '\n' {
            assert(normalize_input(s) == s.subrange(0, s.len()-1));
        } else {
            assert(normalize_input(s) == s);
        }
    }
    
    let len = input.chars().count() as usize;
    if len > 0 && input.chars().nth(len-1).unwrap() == '\n' {
        String::from(&input[0..len-1])
    } else {
        input
    }
}

spec fn is_abc(s: Seq<char>) -> bool {
    s == "ABC"@
}

spec fn is_arc(s: Seq<char>) -> bool {
    s == "ARC"@
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input@)
    ensures result@ == expected_output(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid complex &mut arguments by using ends_with check */
    let normalized_input = normalize_input_impl(input);
    
    proof {
        assert(valid_input(input@));
        let s = normalize_input(input@);
        assert(if is_abc(s) { expected_output(input@) == "ARC\n"@ } else { expected_output(input@) == "ABC\n"@ });
    }
    
    if normalized_input == "ABC" {
        "ARC\n".to_string()
    } else {
        "ABC\n".to_string()
    }
}
// </vc-code>


}

fn main() {}