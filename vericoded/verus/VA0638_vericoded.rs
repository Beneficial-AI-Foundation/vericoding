// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    (input.len() == 3 && input[1] == ' ') || 
    (input.len() == 4 && input[1] == ' ' && input[3] == '\n')
}

spec fn valid_hex_digit(c: char) -> bool {
    c == 'A' || c == 'B' || c == 'C' || c == 'D' || c == 'E' || c == 'F'
}

spec fn valid_input_format(input: Seq<char>) -> bool {
    input.len() >= 3 &&
    valid_input(input) &&
    valid_hex_digit(input[0]) &&
    valid_hex_digit(input[2])
}

spec fn correct_comparison(x: char, y: char, result: Seq<char>) -> bool {
    (result == seq!['<', '\n'] || result == seq!['>', '\n'] || result == seq!['=', '\n']) &&
    (((x as int) < (y as int)) <==> (result == seq!['<', '\n'])) &&
    (((x as int) > (y as int)) <==> (result == seq!['>', '\n'])) &&
    (((x as int) == (y as int)) <==> (result == seq!['=', '\n']))
}
// </vc-preamble>

// <vc-helpers>
fn cmp_result(x: char, y: char) -> (result: Vec<char>)
    ensures
        correct_comparison(x, y, result@),
{
    if x < y {
        vec!['<', '\n']
    } else if x > y {
        vec!['>', '\n']
    } else {
        vec!['=', '\n']
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input_format(stdin_input@)
    ensures correct_comparison(stdin_input@[0], stdin_input@[2], result@)
// </vc-spec>
// <vc-code>
{
    let n = stdin_input.len();
    assert(n >= 3);
    assert(2 < stdin_input.len());
    let x = stdin_input[0];
    let y = stdin_input[2];
    let result_vec = cmp_result(x, y);
    result_vec
}
// </vc-code>


}

fn main() {}