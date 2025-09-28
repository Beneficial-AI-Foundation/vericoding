// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else if n == 4 { seq!['4'] }
    else if n == 5 { seq!['5'] }
    else if n == 6 { seq!['6'] }
    else if n == 7 { seq!['7'] }
    else if n == 8 { seq!['8'] }
    else if n == 9 { seq!['9'] }
    else if n == 10 { seq!['1', '0'] }
    else if n == 11 { seq!['1', '1'] }
    else if n == 12 { seq!['1', '2'] }
    else if n == 13 { seq!['1', '3'] }
    else if n == 14 { seq!['1', '4'] }
    else if n == 15 { seq!['1', '5'] }
    else if n == 16 { seq!['1', '6'] }
    else if n == 17 { seq!['1', '7'] }
    else if n == 18 { seq!['1', '8'] }
    else if n == 19 { seq!['1', '9'] }
    else if n == 20 { seq!['2', '0'] }
    else if n == 21 { seq!['2', '1'] }
    else if n == 22 { seq!['2', '2'] }
    else if n == 23 { seq!['2', '3'] }
    else { seq!['0'] }
}

spec fn valid_input(input: Seq<char>) -> bool {
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b))
}

spec fn contest_start_time(a: int, b: int) -> int {
    (a + b) % 24
}

spec fn correct_output(input: Seq<char>, result: Seq<char>) -> bool {
    valid_input(input) ==> 
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b)) &&
    result == int_to_string(contest_start_time(a, b)) + seq!['\n']
}
// </vc-preamble>

// <vc-helpers>
proof fn contest_start_time_in_range(a: int, b: int)
    requires 0 <= a <= 23 && 0 <= b <= 23
    ensures 0 <= contest_start_time(a, b) <= 23
{
    assert(contest_start_time(a, b) == (a + b) % 24);
    assert(0 <= a + b <= 46);
    assert(0 <= (a + b) % 24 && (a + b) % 24 <= 23);
}

fn parse_digit(c: char) -> (d: u8)
    requires ['0', '9'].contains(c)
    ensures 0 <= d <= 9 && (c == '0' ==> d == 0) && (c == '1' ==> d == 1) && (c == '2' ==> d == 2) && (c == '3' ==> d == 3)
          && (c == '4' ==> d == 4) && (c == '5' ==> d == 5) && (c == '6' ==> d == 6) && (c == '7' ==> d == 7)
          && (c == '8' ==> d == 8) && (c == '9' ==> d == 9)
{
    if c == '0' { 0 }
    else if c == '1' { 1 }
    else if c == '2' { 2 }
    else if c == '3' { 3 }
    else if c == '4' { 4 }
    else if c == '5' { 5 }
    else if c == '6' { 6 }
    else if c == '7' { 7 }
    else if c == '8' { 8 }
    else { 9 }
}

proof fn parse_digit_to_int(c: char) -> (d: int)
    requires ['0', '9'].contains(c)
    ensures 0 <= d <= 9 && (c == '0' ==> d == 0) && (c == '1' ==> d == 1) && (c == '2' ==> d == 2) && (c == '3' ==> d == 3)
          && (c == '4' ==> d == 4) && (c == '5' ==> d == 5) && (c == '6' ==> d == 6) && (c == '7' ==> d == 7)
          && (c == '8' ==> d == 8) && (c == '9' ==> d == 9)
{
    let d_u8 = parse_digit(c);
    assert(0 <= d_u8 <= 9);
    d_u8 as int
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures correct_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion using ghost function */
    let mut a: int = 0;
    let mut b: int = 0;
    let mut found_space = false;
    let mut i: usize = 0;
    let chars_view = input.view();
    
    while i < chars_view.len()
        invariant
            0 <= i <= chars_view.len(),
            !found_space ==> a >= 0, 
            found_space ==> b >= 0
    {
        let c = chars_view.index(i);
        if *c == ' ' {
            found_space = true;
        } else if *c == '\n' {
            break;
        } else if *c >= '0' && *c <= '9' {
            proof {
                let digit_int = parse_digit_to_int(*c);
            }
            let digit = parse_digit_to_int(*c);
            if !found_space {
                a = a * 10 + digit;
            } else {
                b = b * 10 + digit;
            }
        }
        i = i + 1;
    }
    
    assert(0 <= a <= 23 && 0 <= b <= 23);
    let result_time = (a + b) % 24;
    
    let result_str = if result_time == 0 { "0\n" }
        else if result_time == 1 { "1\n" }
        else if result_time == 2 { "2\n" }
        else if result_time == 3 { "3\n" }
        else if result_time == 4 { "4\n" }
        else if result_time == 5 { "5\n" }
        else if result_time == 6 { "6\n" }
        else if result_time == 7 { "7\n" }
        else if result_time == 8 { "8\n" }
        else if result_time == 9 { "9\n" }
        else if result_time == 10 { "10\n" }
        else if result_time == 11 { "11\n" }
        else if result_time == 12 { "12\n" }
        else if result_time == 13 { "13\n" }
        else if result_time == 14 { "14\n" }
        else if result_time == 15 { "15\n" }
        else if result_time == 16 { "16\n" }
        else if result_time == 17 { "17\n" }
        else if result_time == 18 { "18\n" }
        else if result_time == 19 { "19\n" }
        else if result_time == 20 { "20\n" }
        else if result_time == 21 { "21\n" }
        else if result_time == 22 { "22\n" }
        else { "23\n" };
    
    String::from(result_str)
}
// </vc-code>


}

fn main() {}