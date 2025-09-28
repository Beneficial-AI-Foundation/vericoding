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
/* helper modified by LLM (iteration 5): spec helper returning the spec sequence of a runtime String */
spec fn string_to_seq(s: String) -> Seq<char> {
    s@
}
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
{
    /* code modified by LLM (iteration 5): trim newline without using pop, map weather strings to next */
    let s_trim: &str = if input.len() > 0 && input.as_bytes()[input.len()-1] == b'\n' {
        &input[..input.len()-1]
    } else {
        &input[..]
    };
    if s_trim == "Sunny" {
        String::from("Cloudy\n")
    } else if s_trim == "Cloudy" {
        String::from("Rainy\n")
    } else if s_trim == "Rainy" {
        String::from("Sunny\n")
    } else {
        String::new()
    }
}
// </vc-code>


}

fn main() {}