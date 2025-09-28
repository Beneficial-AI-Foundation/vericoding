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
/* helper modified by LLM (iteration 5): change parameter type from int to usize and adjust loop variable */
fn char_at(s: &str, i: usize) -> (c: char)
    requires 0 <= (i as int) < s@.len(),
    ensures c == s@[(i as int)],
{
    let mut iter = s.chars();
    let mut j: usize = 0;
    while let Some(ch) = iter.next()
        invariant j <= i,
        decreases i - j,
    {
        if j == i {
            return ch;
        }
        j += 1;
    }
    unreachable!()
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix int to usize conversion in char_at calls */
{
    let s = stdin_input;
    let month = {
        let c0 = char_at(s, 5 as usize);
        let d0 = (c0 as u32 - '0' as u32);
        let c1 = char_at(s, 6 as usize);
        let d1 = (c1 as u32 - '0' as u32);
        d0 * 10 + d1
    };
    let day = {
        let c0 = char_at(s, 8 as usize);
        let d0 = (c0 as u32 - '0' as u32);
        let c1 = char_at(s, 9 as usize);
        let d1 = (c1 as u32 - '0' as u32);
        d0 * 10 + d1
    };

    if month < 4 || (month == 4 && day <= 30) {
        "Heisei".to_string()
    } else {
        "TBD".to_string()
    }
}
// </vc-code>


}

fn main() {}