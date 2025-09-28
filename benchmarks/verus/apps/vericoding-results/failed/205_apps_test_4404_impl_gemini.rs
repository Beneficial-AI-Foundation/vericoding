// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_valid_date_string(s: Seq<char>, y: int, m: int, d: int) -> bool {
    s.len() >= 10 && 
    s[4] == '/' && s[7] == '/' &&
    string_to_int(s.subrange(0, 4)) == y &&
    string_to_int(s.subrange(5, 7)) == m &&
    string_to_int(s.subrange(8, 10)) == d
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 { 0 }
    else if s.len() == 1 { char_to_digit(s[0]) }
    else if s.len() == 2 { char_to_digit(s[0]) * 10 + char_to_digit(s[1]) }
    else if s.len() == 4 { char_to_digit(s[0]) * 1000 + char_to_digit(s[1]) * 100 + char_to_digit(s[2]) * 10 + char_to_digit(s[3]) }
    else { 0 }
}

spec fn char_to_digit(c: char) -> int {
    if '0' <= c && c <= '9' { (c as int) - ('0' as int) } else { 0 }
}

spec fn valid_input(s: Seq<char>) -> bool {
    exists|y: int, m: int, d: int| is_valid_date_string(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31
}

spec fn correct_output(s: Seq<char>, result: Seq<char>) -> bool {
    exists|y: int, m: int, d: int| is_valid_date_string(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31 && 
    ((m < 4 || (m == 4 && d <= 30)) ==> result == seq!['H', 'e', 'i', 's', 'e', 'i']) && 
    ((m > 4 || (m == 4 && d > 30)) ==> result == seq!['T', 'B', 'D'])
}
// </vc-preamble>

// <vc-helpers>
fn char_to_int_exec(c: char) -> (v: u32)
    ensures v as int == char_to_digit(c),
{
    if c >= '0' && c <= '9' {
        (c as u32) - ('0' as u32)
    } else {
        0
    }
}

fn string_to_int_2_exec(s: &str) -> (v: u32)
    requires s.len() == 2,
    ensures v as int == string_to_int(s@),
{
    let c1 = s.get_char(0);
    let c2 = s.get_char(1);

    let d1 = char_to_int_exec(c1);
    let d2 = char_to_int_exec(c2);
    
    d1 * 10 + d2
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [Use vstd::string::substring to fix compilation error on &str slicing.] */
    let month_string = vstd::string::substring(stdin_input, 5, 7);
    let day_string = vstd::string::substring(stdin_input, 8, 10);
    
    let month = string_to_int_2_exec(&month_string);
    let day = string_to_int_2_exec(&day_string);

    proof {
        let (_y, m, d) = choose |y: int, m: int, d: int| is_valid_date_string(stdin_input@, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31;
        assert(month as int == m);
        assert(day as int == d);
    }

    if month < 4 || (month == 4 && day <= 30) {
        String::from("Heisei")
    } else {
        String::from("TBD")
    }
}
// </vc-code>


}

fn main() {}