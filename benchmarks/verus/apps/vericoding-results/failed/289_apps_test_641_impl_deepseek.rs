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
proof fn lemma_split_once_by_space(s: Seq<char>, i: int) -> (first: Seq<char>, rest: Seq<char>)
    requires
        0 <= i < s.len(),
        s[i] == ' ',
        forall|j: int| 0 <= j < i ==> s[j] != ' ',
    ensures
        first == s.subrange(0, i),
        rest == s.subrange(i + 1, s.len() as int),
{
    (s.subrange(0, i), s.subrange(i + 1, s.len() as int))
}

/* helper modified by LLM (iteration 5): Fixed syntax in spec functions */
spec fn is_digit_char(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn is_digit_pattern(s: Seq<char>) -> bool {
    s.len() > 0 && forall|j: int| 0 <= j < s.len() ==> is_digit_char(s[j])
}

spec fn is_month_pattern(s: Seq<char>) -> bool {
    s == seq!['m', 'o', 'n', 't', 'h']
}

proof fn lemma_split_nonempty(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.subrange(0, i).len() + s.subrange(i + 1, s.len() as int).len() < s.len(),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error in last_part check */
    let char_vec: Vec<char> = input.chars().collect();
    
    let mut trimmed_input: Vec<char> = if char_vec.len() > 0 && char_vec[char_vec.len() - 1] == '\n' {
        char_vec[..char_vec.len() - 1].to_vec()
    } else {
        char_vec
    };
    
    let mut parts: Vec<Vec<char>> = Vec::new();
    let mut current_part: Vec<char> = Vec::new();
    
    for i in 0..trimmed_input.len() {
        if trimmed_input[i] == ' ' {
            if !current_part.is_empty() {
                parts.push(current_part);
                current_part = Vec::new();
            }
        } else {
            current_part.push(trimmed_input[i]);
        }
    }
    
    if !current_part.is_empty() {
        parts.push(current_part);
    }
    
    let last_part: Vec<char> = parts[parts.len() - 1].clone();
    let first_part: Vec<char> = parts[0].clone();
    
    if last_part == vec!['m', 'o', 'n', 't', 'h'] {
        if first_part == vec!['3', '1'] {
            "7\n".to_string()
        } else if first_part == vec!['3', '0'] {
            "11\n".to_string()
        } else {
            "12\n".to_string()
        }
    } else {
        if first_part == vec!['5'] || first_part == vec!['6'] {
            "53\n".to_string()
        } else {
            "52\n".to_string()
        }
    }
}
// </vc-code>


}

fn main() {}