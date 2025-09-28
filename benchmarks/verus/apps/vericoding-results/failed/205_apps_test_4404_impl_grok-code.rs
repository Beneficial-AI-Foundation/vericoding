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
/* helper modified by LLM (iteration 5): Remove assume_specification bypass and add executable parse_int helper to compute integer from string assuming digits. */
fn char_to_digit_exec(c: char) -> (result: i32)
    requires '0' <= c && c <= '9'
    ensures char_to_digit(c) == result as int
{
    (c as u32 - '0' as u32) as i32
}

fn parse_int(s: &str) -> (result: i32)
    requires forall |i: int| 0 <= i < s@.len() ==> '0' <= s@[i] && s@[i] <= '9'
    ensures result as int == string_to_int(s@)
{
    let mut res = 0i32;
    let chars = s.chars();
    proof { assert(chars.forall(|c| '0' <= c <= '9')); }
    for c in chars {
        res = res * 10 + char_to_digit_exec(c);
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use parse_int to compute year, month, day, prove assertions for spec compliance, determine era based on date logic, and return result string. */
{
    let s = stdin_input;
    let y_i32 = parse_int(&s[..4]);
    let m_i32 = parse_int(&s[5..7]);
    let d_i32 = parse_int(&s[8..10]);
    proof {
        let s_seq = s@;
        assert(forall |i: int| (0 <= i < 4) ==> '0' <= s_seq[i] && s_seq[i] <= '9');
        assert(forall |i: int| (5 <= i < 7) ==> '0' <= s_seq[i] && s_seq[i] <= '9');
        assert(forall |i: int| (8 <= i < 10) ==> '0' <= s_seq[i] && s_seq[i] <= '9');
        assert(s_seq[4] == '/');
        assert(s_seq[7] == '/');
        assert(y_i32 as int == string_to_int(s_seq.subrange(0, 4)));
        assert(m_i32 as int == string_to_int(s_seq.subrange(5, 7)));
        assert(d_i32 as int == string_to_int(s_seq.subrange(8, 10)));
        assert(is_valid_date_string(s_seq, y_i32 as int, m_i32 as int, d_i32 as int));
    }
    let is_heisei = (m_i32 < 4) || (m_i32 == 4 && d_i32 <= 30);
    let result = if is_heisei { "Heisei".to_string() } else { "TBD".to_string() };
    result
}
// </vc-code>


}

fn main() {}