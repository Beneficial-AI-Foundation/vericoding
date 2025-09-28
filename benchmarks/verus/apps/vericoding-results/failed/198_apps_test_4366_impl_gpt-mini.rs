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
/* helper modified by LLM (iteration 5): constructs output string for hour with newline */
fn make_output_for(c: int) -> String
    requires
        0 <= c <= 23,
    ensures
        result@ == int_to_string(c) + seq!['\n'],
{
    if c == 0 {
        String::from_str("0\n")
    } else if c == 1 {
        String::from_str("1\n")
    } else if c == 2 {
        String::from_str("2\n")
    } else if c == 3 {
        String::from_str("3\n")
    } else if c == 4 {
        String::from_str("4\n")
    } else if c == 5 {
        String::from_str("5\n")
    } else if c == 6 {
        String::from_str("6\n")
    } else if c == 7 {
        String::from_str("7\n")
    } else if c == 8 {
        String::from_str("8\n")
    } else if c == 9 {
        String::from_str("9\n")
    } else if c == 10 {
        String::from_str("10\n")
    } else if c == 11 {
        String::from_str("11\n")
    } else if c == 12 {
        String::from_str("12\n")
    } else if c == 13 {
        String::from_str("13\n")
    } else if c == 14 {
        String::from_str("14\n")
    } else if c == 15 {
        String::from_str("15\n")
    } else if c == 16 {
        String::from_str("16\n")
    } else if c == 17 {
        String::from_str("17\n")
    } else if c == 18 {
        String::from_str("18\n")
    } else if c == 19 {
        String::from_str("19\n")
    } else if c == 20 {
        String::from_str("20\n")
    } else if c == 21 {
        String::from_str("21\n")
    } else if c == 22 {
        String::from_str("22\n")
    } else if c == 23 {
        String::from_str("23\n")
    } else {
        String::from_str("0\n")
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures correct_output(input@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): parse input and produce output using helper */
{
    if valid_input(input@) {
        let pair = choose |pair: (int, int)|
            0 <= pair.0 <= 23 && 0 <= pair.1 <= 23 &&
            (input@ == int_to_string(pair.0) + seq![' '] + int_to_string(pair.1) + seq!['\n'] ||
             input@ == int_to_string(pair.0) + seq![' '] + int_to_string(pair.1));
        let a = pair.0;
        let b = pair.1;
        let c = contest_start_time(a, b);
        assert(0 <= c && c <= 23);
        make_output_for(c)
    } else {
        String::new()
    }
}

// </vc-code>


}

fn main() {}