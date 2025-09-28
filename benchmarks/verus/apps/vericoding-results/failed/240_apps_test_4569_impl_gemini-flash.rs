// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_weather(weather: Seq<char>) -> bool {
    weather == "Sunny"@ || weather == "Cloudy"@ || weather == "Rainy"@
}

spec fn trim_newline(input: Seq<char>) -> Seq<char> {
    if input.len() > 0 && input[input.len() as int - 1] == '\n' {
        input.subrange(0, input.len() as int - 1)
    } else {
        input
    }
}

spec fn next_weather(weather: Seq<char>) -> Seq<char>
    recommends valid_weather(weather)
{
    if weather == "Sunny"@ { "Cloudy"@ }
    else if weather == "Cloudy"@ { "Rainy"@ }
    else { "Sunny"@ }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures ({
        let trimmed = trim_newline(input@);
        if valid_weather(trimmed) {
            result@ == next_weather(trimmed) + seq!['\n']
        } else {
            result@ == Seq::<char>::empty()
        }
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation errors and use Seq operations for concatenation */
{
    let input_seq = input@;
    let trimmed_input = trim_newline(input_seq);

    if valid_weather(trimmed_input) {
        let next = next_weather(trimmed_input);
        let result_seq = next + seq!['\n'];
        String::from_str(&result_seq)
    } else {
        String::new()
    }
}
// </vc-code>


}

fn main() {}