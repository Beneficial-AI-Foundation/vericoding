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

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Parse date string directly without chars().collect() */
    let s = stdin_input;
    
    // We know from the precondition that the string is valid and has the format YYYY/MM/DD
    // Parse year (positions 0-3)
    let y1 = (s.as_bytes()[0] - b'0') as u32 * 1000;
    let y2 = (s.as_bytes()[1] - b'0') as u32 * 100;
    let y3 = (s.as_bytes()[2] - b'0') as u32 * 10;
    let y4 = (s.as_bytes()[3] - b'0') as u32;
    let year = y1 + y2 + y3 + y4;
    
    // Parse month (positions 5-6)
    let m1 = (s.as_bytes()[5] - b'0') as u32 * 10;
    let m2 = (s.as_bytes()[6] - b'0') as u32;
    let month = m1 + m2;
    
    // Parse day (positions 8-9)
    let d1 = (s.as_bytes()[8] - b'0') as u32 * 10;
    let d2 = (s.as_bytes()[9] - b'0') as u32;
    let day = d1 + d2;
    
    // Check the date and return appropriate result
    if month < 4 || (month == 4 && day <= 30) {
        "Heisei".to_string()
    } else {
        "TBD".to_string()
    }
}
// </vc-code>


}

fn main() {}