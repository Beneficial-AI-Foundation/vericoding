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
    /* code modified by LLM (iteration 3): [replaced unsupported s.ends_with with direct character access on view, and used s.truncate] */
    let mut s = input;
    let original_view = s.view();

    // The precondition `valid_input(original_view)` guarantees `original_view.len() > 0`,
    // so the index access is safe.
    if original_view[original_view.len() - 1] == '\n' {
        let new_len = s.len() - 1;
        s.truncate(new_len);
    }

    assert(s@ == normalize_input(original_view));

    if s.as_str() == "ABC" {
        assert(s@ == "ABC"@);
        assert(expected_output(original_view) == "ARC\n"@);
        String::from("ARC\n")
    } else {
        // From `requires valid_input`, we know `normalize_input(original_view)` is "ABC" or "ARC".
        // Since s@ == normalize_input(...) and s@ is not "ABC", it must be "ARC".
        assert(s@ == "ARC"@);
        assert(expected_output(original_view) == "ABC\n"@);
        String::from("ABC\n")
    }
}
// </vc-code>


}

fn main() {}