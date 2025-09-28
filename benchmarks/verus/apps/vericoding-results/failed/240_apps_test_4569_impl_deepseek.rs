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

proof fn lemma_next_weather_valid(weather: Seq<char>)
    requires
        valid_weather(weather),
    ensures
        valid_weather(next_weather(weather)),
{
}

proof fn lemma_trim_newline_preserves_validity(input: Seq<char>)
    requires
        valid_weather(input),
    ensures
        valid_weather(trim_newline(input)),
{
}

proof fn lemma_range_iteration_with_nat(n: nat)
    ensures
        forall |i: nat| i < n ==> true,
{
    if n > 0 {
        lemma_range_iteration_with_nat((n - 1) as nat);
    }
}

fn next_weather_ghost(weather: Seq<char>) -> (result: Seq<char>)
    requires
        valid_weather(weather),
    ensures
        result == next_weather(weather),
{
    if weather =~= "Sunny"@ { "Cloudy"@ }
    else if weather =~= "Cloudy"@ { "Rainy"@ }
    else { "Sunny"@ }
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
    /* code modified by LLM (iteration 5): fix sequence comparison and nat/int conversions */
    let chars: Vec<char> = input.chars().collect();
    let seq_chars = chars@;
    let trimmed = trim_newline(seq_chars);
    
    if valid_weather(trimmed) {
        proof {
            lemma_next_weather_valid(trimmed);
        }
        let next = next_weather_ghost(trimmed);
        let ghost len_nat = next.len();
        let mut result_chars: Vec<char> = Vec::new();
        proof {
            lemma_range_iteration_with_nat(len_nat);
            let mut i: int = 0;
            while i < len_nat as int
                invariant
                    0 <= i <= len_nat as int,
                    result_chars@.len() == i as nat,
                    forall |j: int| 0 <= j < i ==> result_chars@[j as nat] == next[j as nat],
            {
                result_chars.push(next[i as nat]);
                i = i + 1;
            }
        }
        result_chars.push('\n');
        String::from_iter(result_chars)
    } else {
        String::new()
    }
}
// </vc-code>


}

fn main() {}