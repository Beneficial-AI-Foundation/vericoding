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
fn exec_split_on_space(s: Seq<char>) -> Vec<Seq<char>> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < s.len() {
        if s[i] == ' ' {
            parts.push(s.subrange(start, i - start));
            start = i + 1;
        }
        i += 1;
    }
    parts.push(s.subrange(start, s.len() - start));
    parts
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    let input_seq = input@;
    let trimmed_seq = if input_seq.len() > 0 && input_seq[input_seq.len()-1] == '\n' {
        input_seq.subrange(0, input_seq.len()-1)
    } else {
        input_seq
    };
    let parts = exec_split_on_space(trimmed_seq);
    let last_part = parts[parts.len()-1];
    let first_part = parts[0];
    let result_seq = if last_part == seq!['m','o','n','t','h'] {
        if first_part == seq!['3','1'] { seq!['7','\n'] }
        else if first_part == seq!['3','0'] { seq!['1','1','\n'] }
        else { seq!['1','2','\n'] }
    } else {
        if first_part == seq!['5'] || first_part == seq!['6'] { seq!['5','3','\n'] }
        else { seq!['5','2','\n'] }
    };
    let mut result_string = String::new();
    for c in result_seq {
        result_string.push(c);
    }
    result_string
}
// </vc-code>


}

fn main() {}