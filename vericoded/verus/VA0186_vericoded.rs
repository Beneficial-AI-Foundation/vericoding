// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 2 && 
    '0' <= input[0] <= '9' && 
    '0' <= input[1] <= '9' &&
    (input[input.len() - 1] == '\n' || (input[0] != '\n' && input[1] != '\n'))
}

spec fn good_digit_count(digit: char) -> int 
    recommends '0' <= digit <= '9'
{
    if digit == '0' { 2 }
    else if digit == '1' { 7 }
    else if digit == '2' { 2 }
    else if digit == '3' { 3 }
    else if digit == '4' { 3 }
    else if digit == '5' { 4 }
    else if digit == '6' { 2 }
    else if digit == '7' { 5 }
    else if digit == '8' { 1 }
    else { 2 }
}

spec fn compute_total_good_count(input: Seq<char>) -> int 
    recommends valid_input(input)
{
    good_digit_count(input[0]) * good_digit_count(input[1])
}

spec fn valid_output(result: Seq<char>, expected_count: int) -> bool {
    result.len() >= 2 && 
    result[result.len() - 1] == '\n' &&
    (forall|c: char| result.contains(c) ==> c == '\n' || ('0' <= c <= '9')) &&
    expected_count >= 1 && expected_count <= 49
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): changed return type to i32 and removed int casts */
exec fn good_digit_count_exec(digit: char) -> (count: i32)
    requires '0' <= digit <= '9'
    ensures count as int == good_digit_count(digit)
{
    if digit == '0' { 2 }
    else if digit == '1' { 7 }
    else if digit == '2' { 2 }
    else if digit == '3' { 3 }
    else if digit == '4' { 3 }
    else if digit == '5' { 4 }
    else if digit == '6' { 2 }
    else if digit == '7' { 5 }
    else if digit == '8' { 1 }
    else { 2 } // for '9'
}

/* helper modified by LLM (iteration 5): cast n to int in ensures clause for array indexing */
exec fn int_to_digit_char(n: i32) -> (c: char)
    requires 0 <= n <= 9
    ensures c == ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'][n as int]
{
    if n == 0 { '0' }
    else if n == 1 { '1' }
    else if n == 2 { '2' }
    else if n == 3 { '3' }
    else if n == 4 { '4' }
    else if n == 5 { '5' }
    else if n == 6 { '6' }
    else if n == 7 { '7' }
    else if n == 8 { '8' }
    else { '9' }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(result@, compute_total_good_count(input@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): replaced int with i32 for arithmetic operations */
{
    let d0 = input[0];
    let d1 = input[1];
    let count0 = good_digit_count_exec(d0);
    let count1 = good_digit_count_exec(d1);
    let product = count0 * count1;

    // Now break product into tens and ones
    let tens = product / 10;
    let ones = product % 10;

    let mut result = Vec::new();
    if tens > 0 {
        // Convert tens to char: tens is in [1,4]
        let tens_char = int_to_digit_char(tens);
        result.push(tens_char);
    }
    // Convert ones to char: ones is in [0,9]
    let ones_char = int_to_digit_char(ones);
    result.push(ones_char);
    result.push('\n');

    result
}
// </vc-code>


}

fn main() {}