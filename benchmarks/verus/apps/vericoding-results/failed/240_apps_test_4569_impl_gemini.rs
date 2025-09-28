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
{
    /* code modified by LLM (iteration 5): replaced unsupported strip_suffix with supported ends_with and pop methods */
    proof {
        verus_builtin::reveal_strlit("Sunny");
        verus_builtin::reveal_strlit("Cloudy");
        verus_builtin::reveal_strlit("Rainy");
        verus_builtin::reveal_strlit("\n");
        verus_builtin::reveal_strlit("Cloudy\n");
        verus_builtin::reveal_strlit("Rainy\n");
        verus_builtin::reveal_strlit("Sunny\n");
    }

    let mut trimmed = input;
    if trimmed.ends_with("\n") {
        trimmed.pop();
    }

    if trimmed.as_str() == "Sunny" {
        String::from("Cloudy\n")
    } else if trimmed.as_str() == "Cloudy" {
        String::from("Rainy\n")
    } else if trimmed.as_str() == "Rainy" {
        String::from("Sunny\n")
    } else {
        String::new()
    }
}
// </vc-code>


}

fn main() {}