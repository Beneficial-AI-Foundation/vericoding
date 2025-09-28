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
    /* code modified by LLM (iteration 5): manually build vector from string without using collect() */
    let mut input_chars: Vec<char> = Vec::new();
    let input_len = input.unicode_len();
    let mut i: usize = 0;
    while i < input_len
        invariant
            i <= input_len,
            input_chars.len() == i,
            input_chars@ == input@.subrange(0, i as int),
    {
        let ch = input.get_char(i);
        input_chars.push(ch);
        i = i + 1;
    }
    
    proof {
        assert(input_chars@ == input@);
    }
    
    let len = input_chars.len();
    
    // Check if input ends with newline and needs trimming
    if len > 0 && input_chars[len - 1] == '\n' {
        // Build trimmed string
        let mut trimmed_chars: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < len - 1
            invariant
                j <= len - 1,
                trimmed_chars.len() == j,
                trimmed_chars@ == input@.subrange(0, j as int),
        {
            trimmed_chars.push(input_chars[j]);
            j = j + 1;
        }
        
        proof {
            assert(trimmed_chars@ == input@.subrange(0, (len - 1) as int));
            assert(input@[input@.len() - 1] == '\n');
            assert(trimmed_chars@ == trim_newline(input@));
        }
        
        // Check weather patterns using character comparison
        if trimmed_chars.len() == 5 &&
           trimmed_chars[0] == 'S' && trimmed_chars[1] == 'u' && 
           trimmed_chars[2] == 'n' && trimmed_chars[3] == 'n' && 
           trimmed_chars[4] == 'y' {
            proof {
                assert(trimmed_chars@ == "Sunny"@);
                assert(valid_weather(trim_newline(input@)));
                assert(next_weather(trim_newline(input@)) == "Cloudy"@);
            }
            return "Cloudy\n".to_string();
        } else if trimmed_chars.len() == 6 &&
                  trimmed_chars[0] == 'C' && trimmed_chars[1] == 'l' &&
                  trimmed_chars[2] == 'o' && trimmed_chars[3] == 'u' &&
                  trimmed_chars[4] == 'd' && trimmed_chars[5] == 'y' {
            proof {
                assert(trimmed_chars@ == "Cloudy"@);
                assert(valid_weather(trim_newline(input@)));
                assert(next_weather(trim_newline(input@)) == "Rainy"@);
            }
            return "Rainy\n".to_string();
        } else if trimmed_chars.len() == 5 &&
                  trimmed_chars[0] == 'R' && trimmed_chars[1] == 'a' &&
                  trimmed_chars[2] == 'i' && trimmed_chars[3] == 'n' &&
                  trimmed_chars[4] == 'y' {
            proof {
                assert(trimmed_chars@ == "Rainy"@);
                assert(valid_weather(trim_newline(input@)));
                assert(next_weather(trim_newline(input@)) == "Sunny"@);
            }
            return "Sunny\n".to_string();
        } else {
            return "".to_string();
        }
    } else {
        // No newline to trim, check input directly
        if input_chars.len() == 5 &&
           input_chars[0] == 'S' && input_chars[1] == 'u' &&
           input_chars[2] == 'n' && input_chars[3] == 'n' &&
           input_chars[4] == 'y' {
            proof {
                assert(input@ == "Sunny"@);
                assert(trim_newline(input@) == input@);
                assert(valid_weather(trim_newline(input@)));
                assert(next_weather(trim_newline(input@)) == "Cloudy"@);
            }
            return "Cloudy\n".to_string();
        } else if input_chars.len() == 6 &&
                  input_chars[0] == 'C' && input_chars[1] == 'l' &&
                  input_chars[2] == 'o' && input_chars[3] == 'u' &&
                  input_chars[4] == 'd' && input_chars[5] == 'y' {
            proof {
                assert(input@ == "Cloudy"@);
                assert(trim_newline(input@) == input@);
                assert(valid_weather(trim_newline(input@)));
                assert(next_weather(trim_newline(input@)) == "Rainy"@);
            }
            return "Rainy\n".to_string();
        } else if input_chars.len() == 5 &&
                  input_chars[0] == 'R' && input_chars[1] == 'a' &&
                  input_chars[2] == 'i' && input_chars[3] == 'n' &&
                  input_chars[4] == 'y' {
            proof {
                assert(input@ == "Rainy"@);
                assert(trim_newline(input@) == input@);
                assert(valid_weather(trim_newline(input@)));
                assert(next_weather(trim_newline(input@)) == "Sunny"@);
            }
            return "Sunny\n".to_string();
        } else {
            return "".to_string();
        }
    }
}
// </vc-code>


}

fn main() {}