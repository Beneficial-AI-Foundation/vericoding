// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_on_space(s: Seq<char>) -> Seq<Seq<char>>;

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    ({
        let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
        let parts = split_on_space(trimmed);
        parts.len() >= 1
    })
}

spec fn get_expected_result(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
    let parts = split_on_space(trimmed);
    if parts[parts.len() as int - 1] == seq!['m', 'o', 'n', 't', 'h'] {
        if parts[0] == seq!['3', '1'] { seq!['7', '\n'] }
        else if parts[0] == seq!['3', '0'] { seq!['1', '1', '\n'] }
        else { seq!['1', '2', '\n'] }
    } else {
        if parts[0] == seq!['5'] || parts[0] == seq!['6'] { seq!['5', '3', '\n'] }
        else { seq!['5', '2', '\n'] }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): implementing helper functions for string splitting */
spec fn find_first_space(s: Seq<char>, start: int) -> int
    decreases (s.len() as int - start)
{
    if start >= s.len() {
        -1
    } else if s[start] == ' ' {
        start
    } else {
        find_first_space(s, start + 1)
    }
}

spec fn split_on_space(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let index = find_first_space(s, 0);
        if index == -1 {
            seq![s]
        } else {
            let first_part = s.subrange(0, index as nat);
            if first_part.len() == 0 {
                split_on_space(s.subrange(index + 1, s.len() as int))
            } else {
                let rest = s.subrange(index + 1, s.len() as int);
                seq![first_part] + split_on_space(rest)
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implementing solve method with fixed string logic matching spec */
    let trimmed: &str = if input.ends_with('\n') { &input[..input.len() - 1] } else { input };
    let parts: Vec<&str> = trimmed.split_whitespace().collect();
    let first_part = parts[0];
    let last_part = parts[parts.len() - 1];
    let result = if last_part == "month" {
        if first_part == "31" {
            "7\n".to_string()
        } else if first_part == "30" {
            "11\n".to_string()
        } else {
            "12\n".to_string()
        }
    } else {
        if first_part == "5" || first_part == "6" {
            "53\n".to_string()
        } else {
            "52\n".to_string()
        }
    };
    result
}
// </vc-code>


}

fn main() {}