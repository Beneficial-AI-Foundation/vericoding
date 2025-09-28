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

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input@)
    ensures result@ == expected_output(input@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed type mismatch in result assignment by ensuring all branches return String */
    let normalized: String = if input.ends_with('\n') {
        input[..input.len() - 1].to_string()
    } else {
        input
    };
    let result = if normalized == "ABC" {
        "ARC\n".to_string()
    } else if normalized == "ARC" {
        "ABC\n".to_string()
    } else {
        "Error".to_string() // though spec ensures valid
    };
    result
}
// </vc-code>


}

fn main() {}