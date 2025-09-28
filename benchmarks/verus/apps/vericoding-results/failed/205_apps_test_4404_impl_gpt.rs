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
/* helper modified by LLM (iteration 5): helper to map a char to its digit value, aligned with spec char_to_digit */
fn digit_of(c: char) -> (res: u64)
    ensures
        res as int == char_to_digit(c),
{
    if '0' <= c && c <= '9' {
        (c as u64) - ('0' as u64)
    } else {
        0
    }
}

/* helper modified by LLM (iteration 5): parse two consecutive digits at position i into a u64, matching string_to_int on the spec view */
fn parse2(s: &str, i: usize) -> (res: u64)
    requires
        s@.len() >= i + 2,
    ensures
        res as int == string_to_int(s@.subrange(i as int, i as int + 2)),
{
    let mut it = s.chars();
    let mut idx: usize = 0;
    let mut c0: char = '\0';
    let mut c1: char = '\0';
    while idx < i
        invariant
            idx <= i,
            s@.len() >= i + 2,
        decreases i - idx
    {
        let _ = it.next().unwrap();
        idx += 1;
    }
    c0 = it.next().unwrap();
    c1 = it.next().unwrap();
    let d0 = digit_of(c0);
    let d1 = digit_of(c1);
    d0 * 10 + d1
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures correct_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid String::new; construct result using String::from literals after parsing month/day */
    proof {
        let t = choose|t: (int, int, int)|
            is_valid_date_string(stdin_input@, t.0, t.1, t.2) && t.0 == 2019 && 1 <= t.1 <= 12 && 1 <= t.2 <= 31;
        assert(is_valid_date_string(stdin_input@, t.0, t.1, t.2));
        assert(stdin_input@.len() >= 10);
    }

    let m: u64 = parse2(stdin_input, 5);
    let d: u64 = parse2(stdin_input, 8);

    let cond: bool = m < 4u64 || (m == 4u64 && d <= 30u64);

    let result: String = if cond {
        String::from("Heisei")
    } else {
        String::from("TBD")
    };

    proof {
        let t = choose|t: (int, int, int)|
            is_valid_date_string(stdin_input@, t.0, t.1, t.2) && t.0 == 2019 && 1 <= t.1 <= 12 && 1 <= t.2 <= 31;
        assert(is_valid_date_string(stdin_input@, t.0, t.1, t.2));
        assert(m as int == string_to_int(stdin_input@.subrange(5, 7)));
        assert(d as int == string_to_int(stdin_input@.subrange(8, 10)));
        assert(string_to_int(stdin_input@.subrange(5, 7)) == t.1);
        assert(string_to_int(stdin_input@.subrange(8, 10)) == t.2);
        assert(m as int == t.1);
        assert(d as int == t.2);
        if cond {
            assert(t.1 < 4 || (t.1 == 4 && t.2 <= 30));
            assert(result@ == seq!['H','e','i','s','e','i']);
        } else {
            assert(t.1 > 4 || (t.1 == 4 && t.2 > 30));
            assert(result@ == seq!['T','B','D']);
        }
    }

    result
}
// </vc-code>


}

fn main() {}