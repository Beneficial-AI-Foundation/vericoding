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
/* helper modified by LLM (iteration 5): add helper to safely get last character */
fn get_last_char(s: &str) -> (result: Option<char>)
    ensures
        s.len() == 0 ==> result.is_none(),
        s.len() > 0 ==> result == Some(s@[s@.len() - 1 as int]),
{
    s.chars().last()
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input@)
    ensures result@ == expected_output(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix nat comparison type error */
    let input_seq = input@;
    let len = input_seq.len();
    
    let normalized_str = if len > 0nat && get_last_char(&input) == Some('\n') {
        input.trim_end_matches('\n')
    } else {
        input.as_str()
    };
    
    if normalized_str == "ABC" {
        "ARC\n".to_string()
    } else {
        "ABC\n".to_string()
    }
}
// </vc-code>


}

fn main() {}