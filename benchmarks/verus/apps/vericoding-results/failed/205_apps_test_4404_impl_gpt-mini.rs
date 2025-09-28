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
/* helper modified by LLM (iteration 5): relate 2-char subranges to string_to_int for month and day */
proof fn string_to_int_positions(s: Seq<char>)
    requires
        s.len() >= 10,
    ensures
        string_to_int(s.subrange(5, 7)) == char_to_digit(s[5]) * 10 + char_to_digit(s[6]),
        string_to_int(s.subrange(8, 10)) == char_to_digit(s[8]) * 10 + char_to_digit(s[9]),
{
    proof {
        assert(s.subrange(5, 7).len() == 2);
        assert(string_to_int(s.subrange(5, 7)) == char_to_digit(s[5]) * 10 + char_to_digit(s[6]));
        assert(s.subrange(8, 10).len() == 2);
        assert(string_to_int(s.subrange(8, 10)) == char_to_digit(s[8]) * 10 + char_to_digit(s[9]));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute month/day from ASCII digits without using b'0' byte literal */
    let b = stdin_input.as_bytes();
    let m = (b[5] as i32 - '0' as i32) * 10 + (b[6] as i32 - '0' as i32);
    let d = (b[8] as i32 - '0' as i32) * 10 + (b[9] as i32 - '0' as i32);
    let result = if m < 4 || (m == 4 && d <= 30) {
        String::from("Heisei")
    } else {
        String::from("TBD")
    };
    result
}

// </vc-code>


}

fn main() {}