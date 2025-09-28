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
/* helper modified by LLM (iteration 2): helper function to compare hex digits in exec code */
fn compare_hex_digits(x: char, y: char) -> (result: char)
    requires valid_hex_digit(x), valid_hex_digit(y)
    ensures
        ((x as int) < (y as int)) <==> (result == '<'),
        ((x as int) > (y as int)) <==> (result == '>'),
        ((x as int) == (y as int)) <==> (result == '=')
{
    if x < y {
        '<'
    } else if x > y {
        '>'
    } else {
        '='
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
    /* code modified by LLM (iteration 2): use char comparison instead of int casting in exec code */
    let x = stdin_input[0];
    let y = stdin_input[2];
    
    let comparison_result = compare_hex_digits(x, y);
    let result = vec![comparison_result, '\n'];
    
    proof {
        assert(valid_hex_digit(x));
        assert(valid_hex_digit(y));
        assert(result@ == seq![comparison_result, '\n']);
    }
    
    result
}
// </vc-code>


}

fn main() {}