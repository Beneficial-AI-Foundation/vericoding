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

// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using string slice patterns to avoid unsupported index operator */
    let input_str = input;
    let trimmed_str = if input_str.len() > 0 && input_str.chars().last() == Some('\n') {
        let len = input_str.len();
        &input_str[0..len - 1]
    } else {
        input_str
    };
    
    let parts: Vec<&str> = trimmed_str.split(' ').collect();
    
    if parts.len() > 0 && parts[parts.len() - 1] == "month" {
        if parts[0] == "31" {
            return "7\n".to_string();
        } else if parts[0] == "30" {
            return "11\n".to_string();
        } else {
            return "12\n".to_string();
        }
    } else {
        if parts.len() > 0 && (parts[0] == "5" || parts[0] == "6") {
            return "53\n".to_string();
        } else {
            return "52\n".to_string();
        }
    }
}
// </vc-code>


}

fn main() {}