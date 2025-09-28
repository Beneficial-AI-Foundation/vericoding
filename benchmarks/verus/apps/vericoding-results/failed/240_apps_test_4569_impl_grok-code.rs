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
/* helper modified by LLM (iteration 5): Fixed executable trim_newline to avoid forbidden string slicing, using chars().take().collect() for Verus exec code compatibility */
fn trim_newline_exec(s: &String) -> String
    ensures
        s@ == trim_newline(s@)
{
    proof { }
    if s.is_empty() || s.chars().last() != Some('\n') {
        s.clone()
    } else {
        s.chars().take(s.len() - 1).collect::<String>()
    }
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
/* code modified by LLM (iteration 5): Implemented solve function using fixed executable helper, with logic to trim input, validate and compute next weather, and format output string */
{
    let trimmed = trim_newline_exec(&input);
    if trimmed == "Sunny" || trimmed == "Cloudy" || trimmed == "Rainy" {
        let next = if trimmed == "Sunny" { "Cloudy" }
                   else if trimmed == "Cloudy" { "Rainy" }
                   else { "Sunny" }.to_string() + "\n";
        next
    } else {
        "".to_string()
    }
}
// </vc-code>


}

fn main() {}