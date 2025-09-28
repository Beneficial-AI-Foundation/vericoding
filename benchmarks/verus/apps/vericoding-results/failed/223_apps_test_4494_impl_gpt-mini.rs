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
/* helper modified by LLM (iteration 5): create ABC\n string */
fn make_abc_newline() -> (result: String)
    ensures
        result@ == "ABC\n"@,
{
    let s = "ABC\n".to_string();
    s
}

/* helper modified by LLM (iteration 5): create ARC\n string */
fn make_arc_newline() -> (result: String)
    ensures
        result@ == "ARC\n"@,
{
    let s = "ARC\n".to_string();
    s
}

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input@)
    ensures result@ == expected_output(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute normalized input and return opposite string */
    let mut s = input.clone();
    if s.ends_with("\n") {
        s.pop();
    }
    if s == "ABC" {
        make_arc_newline()
    } else {
        make_abc_newline()
    }
}

// </vc-code>


}

fn main() {}