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
/* helper modified by LLM (iteration 5): relate input literals to expected_output */
proof fn lemma_expected_from_literal(input: Seq<char>)
    ensures
        input == "ABC"@ ==> expected_output(input) == "ARC\n"@,
        input == "ABC\n"@ ==> expected_output(input) == "ARC\n"@,
        input == "ARC"@ ==> expected_output(input) == "ABC\n"@,
        input == "ARC\n"@ ==> expected_output(input) == "ABC\n"@,
{
    if input == "ABC"@ {
        assert(normalize_input(input) == "ABC"@);
        assert(expected_output(input) == "ARC\n"@);
    }
    if input == "ABC\n"@ {
        assert(normalize_input(input) == "ABC"@);
        assert(expected_output(input) == "ARC\n"@);
    }
    if input == "ARC"@ {
        assert(normalize_input(input) == "ARC"@);
        assert(expected_output(input) == "ABC\n"@);
    }
    if input == "ARC\n"@ {
        assert(normalize_input(input) == "ARC"@);
        assert(expected_output(input) == "ABC\n"@);
    }
}

/* helper modified by LLM (iteration 5): view of as_str equals view of String */
proof fn lemma_string_as_str_view(s: &String)
    ensures s.as_str()@ == s@,
{
    assert(s.as_str()@ == s@);
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input@)
    ensures result@ == expected_output(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use &str comparisons and prove correspondence to expected_output */
    if input.as_str() == "ABC" || input.as_str() == "ABC\n" {
        let mut r = String::new();
        r.push('A');
        r.push('R');
        r.push('C');
        r.push('\n');
        proof {
            lemma_expected_from_literal(input@);
            lemma_string_as_str_view(&input);
            if input.as_str() == "ABC" {
                assert(input.as_str()@ == "ABC"@);
                assert(input@ == "ABC"@);
            } else {
                assert(input.as_str() == "ABC\n");
                assert(input.as_str()@ == "ABC\n"@);
                assert(input@ == "ABC\n"@);
            }
            assert(expected_output(input@) == "ARC\n"@);
        }
        r
    } else {
        let mut r = String::new();
        r.push('A');
        r.push('B');
        r.push('C');
        r.push('\n');
        proof {
            lemma_expected_from_literal(input@);
            lemma_string_as_str_view(&input);
            if input.as_str() == "ARC" {
                assert(input.as_str()@ == "ARC"@);
                assert(input@ == "ARC"@);
            } else {
                assert(input.as_str() == "ARC\n");
                assert(input.as_str()@ == "ARC\n"@);
                assert(input@ == "ARC\n"@);
            }
            assert(expected_output(input@) == "ABC\n"@);
        }
        r
    }
}
// </vc-code>


}

fn main() {}