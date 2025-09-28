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

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(result@, compute_total_good_count(input@))
// </vc-spec>
// <vc-code>
{
    let digit1 = input[0];
    let digit2 = input[1];
    
    let count1 = if digit1 == '0' { 2 }
        else if digit1 == '1' { 7 }
        else if digit1 == '2' { 2 }
        else if digit1 == '3' { 3 }
        else if digit1 == '4' { 3 }
        else if digit1 == '5' { 4 }
        else if digit1 == '6' { 2 }
        else if digit1 == '7' { 5 }
        else if digit1 == '8' { 1 }
        else { 2 };
    
    let count2 = if digit2 == '0' { 2 }
        else if digit2 == '1' { 7 }
        else if digit2 == '2' { 2 }
        else if digit2 == '3' { 3 }
        else if digit2 == '4' { 3 }
        else if digit2 == '5' { 4 }
        else if digit2 == '6' { 2 }
        else if digit2 == '7' { 5 }
        else if digit2 == '8' { 1 }
        else { 2 };
    
    let total = count1 * count2;
    
    let mut result = Vec::new();
    
    if total >= 10 {
        let tens_digit = ((total / 10) as u8 + '0' as u8) as char;
        result.push(tens_digit);
    }
    
    let ones_digit = ((total % 10) as u8 + '0' as u8) as char;
    result.push(ones_digit);
    result.push('\n');
    
    result
}
// </vc-code>


}

fn main() {}