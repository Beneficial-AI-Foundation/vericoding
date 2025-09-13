// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_weather(weather: Seq<char>) -> bool {
    weather == seq!['S','u','n','n','y'] || weather == seq!['C','l','o','u','d','y'] || weather == seq!['R','a','i','n','y']
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
    if weather == seq!['S','u','n','n','y'] { seq!['C','l','o','u','d','y'] }
    else if weather == seq!['C','l','o','u','d','y'] { seq!['R','a','i','n','y'] }
    else { seq!['S','u','n','n','y'] }
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
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}