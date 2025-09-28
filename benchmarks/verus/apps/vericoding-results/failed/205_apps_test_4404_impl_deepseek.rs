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
proof fn find_valid_date(s: Seq<char>) -> (y: int, m: int, d: int)
    requires valid_input(s)
    ensures is_valid_date_string(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31
{
    /* helper modified by LLM (iteration 5): Fixed return type syntax error */
    assert(exists|y: int, m: int, d: int| is_valid_date_string(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31);
    
    let (y, m, d) = choose|y: int, m: int, d: int| 
        is_valid_date_string(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31;
    (y, m, d)
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed verification */
    assert(valid_input(stdin_input@));
    
    let (y, m, d) = find_valid_date(stdin_input@);
    
    proof {
        assert(is_valid_date_string(stdin_input@, y, m, d));
        assert(y == 2019 && 1 <= m <= 12 && 1 <= d <= 31);
    }
    
    let result_str = if m < 4 || (m == 4 && d <= 30) {
        String::from_str("Heisei").unwrap()
    } else {
        String::from_str("TBD").unwrap()
    };
    
    proof {
        if m < 4 || (m == 4 && d <= 30) {
            assert(result_str@ == seq!['H', 'e', 'i', 's', 'e', 'i']);
        } else {
            assert(result_str@ == seq!['T', 'B', 'D']);
        }
        assert(correct_output(stdin_input@, result_str@));
    }
    
    result_str
}
// </vc-code>


}

fn main() {}