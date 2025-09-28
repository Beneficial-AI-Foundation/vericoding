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
/* code modified by LLM (iteration 5): Fixed cast to int by removing it, as subrange expects `nat` indices. */
{
    let s_char_seq = input@;
    let normalized_s = if (s_char_seq.len() > 0 && s_char_seq.index(s_char_seq.len() - 1) == '\n') {
        s_char_seq.subrange(0, s_char_seq.len() - 1)
    } else {
        s_char_seq
    };

    if normalized_s == Seq::from_str("ABC") {
        "ARC\n".to_string()
    } else {
        "ABC\n".to_string()
    }
}
// </vc-code>


}

fn main() {}