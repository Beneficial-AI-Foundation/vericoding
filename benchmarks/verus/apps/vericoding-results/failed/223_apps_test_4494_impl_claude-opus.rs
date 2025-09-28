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
    /* code modified by LLM (iteration 5): Fixed type mismatches with nat and string operations */
    let input_view = input@;
    let len = input_view.len();
    
    let has_newline = len > 0 && input_view[len - 1nat] == '\n';
    
    let s = if has_newline {
        input.substring_char(0, (len - 1nat) as usize)
    } else {
        input.as_str()
    };
    
    proof {
        if has_newline {
            assert(s@ == input@.subrange(0, input@.len() - 1));
        } else {
            assert(s@ == input@);
        }
        assert(s@ == normalize_input(input@));
    }
    
    let result = if s == "ABC" {
        "ARC\n".to_string()
    } else {
        "ABC\n".to_string()
    };
    
    proof {
        assert(valid_input(input@));
        let normalized = normalize_input(input@);
        assert(s@ == normalized);
        if s == "ABC" {
            assert(s@ == "ABC"@);
            assert(normalized == "ABC"@);
            assert(result@ == "ARC\n"@);
            assert(expected_output(input@) == "ARC\n"@);
        } else {
            assert(s@ == "ARC"@);
            assert(normalized == "ARC"@);
            assert(result@ == "ABC\n"@);
            assert(expected_output(input@) == "ABC\n"@);
        }
        assert(result@ == expected_output(input@));
    }
    
    result
}
// </vc-code>


}

fn main() {}