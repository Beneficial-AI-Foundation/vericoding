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
/* helper modified by LLM (iteration 5): removed problematic equality function and added string matching helpers */
fn string_to_seq_sunny() -> (result: Seq<char>)
    ensures result == "Sunny"@
{
    "Sunny"@
}

fn string_to_seq_cloudy() -> (result: Seq<char>)
    ensures result == "Cloudy"@
{
    "Cloudy"@
}

fn string_to_seq_rainy() -> (result: Seq<char>)
    ensures result == "Rainy"@
{
    "Rainy"@
}

fn lemma_valid_weather_cases(weather: Seq<char>)
    requires valid_weather(weather)
    ensures
        weather == "Sunny"@ || weather == "Cloudy"@ || weather == "Rainy"@
{
}

fn lemma_next_weather_valid(weather: Seq<char>)
    requires valid_weather(weather)
    ensures valid_weather(next_weather(weather))
{
}

fn lemma_trim_newline_properties(input: Seq<char>)
    ensures
        trim_newline(input).len() <= input.len(),
        input.len() > 0 && input[input.len() as int - 1] == '\n' ==> trim_newline(input) == input.subrange(0, input.len() as int - 1),
        (input.len() == 0 || input[input.len() as int - 1] != '\n') ==> trim_newline(input) == input
{
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
    /* code modified by LLM (iteration 5): use direct sequence equality without helper function */
    let trimmed = trim_newline(input@);
    
    if trimmed =~= "Sunny"@ {
        return String::from("Cloudy\n");
    } else if trimmed =~= "Cloudy"@ {
        return String::from("Rainy\n");
    } else if trimmed =~= "Rainy"@ {
        return String::from("Sunny\n");
    } else {
        return String::new();
    }
}
// </vc-code>


}

fn main() {}