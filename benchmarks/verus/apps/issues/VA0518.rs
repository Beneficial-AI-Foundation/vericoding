// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn split_string(s: Seq<char>, delimiter: char) -> Seq<Seq<char>> { seq![] }

spec fn str_to_int(s: Seq<char>) -> int { 0 }

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    exists|lines: Seq<Seq<char>>| lines == split_string(input, '\n') && lines.len() > 0 &&
    exists|parts: Seq<Seq<char>>| parts == split_string(lines[0], ' ') && parts.len() == 2 &&
    {
        let n = str_to_int(parts[0]);
        let m = str_to_int(parts[1]);
        1 <= n <= 100 && 0 <= m <= n
    }
}

spec fn extract_n(input: Seq<char>) -> int {
    let lines = split_string(input, '\n');
    let parts = split_string(lines[0], ' ');
    str_to_int(parts[0])
}

spec fn extract_m(input: Seq<char>) -> int {
    let lines = split_string(input, '\n');
    let parts = split_string(lines[0], ' ');
    str_to_int(parts[1])
}

spec fn correct_output(input: Seq<char>, result: Seq<char>) -> bool {
    let n = extract_n(input);
    let m = extract_m(input);
    (n == m ==> result == seq!['Y', 'e', 's']) && (n != m ==> result == seq!['N', 'o'])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
requires 
    valid_input(input@)
ensures 
    correct_output(input@, result@),
    result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o']
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}