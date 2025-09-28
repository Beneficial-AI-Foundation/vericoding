// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    is_valid_integer_string(s) && 
    { let n = parse_integer(s); 0 <= n <= 99 }
}

spec fn correct_english_word(n: int) -> Seq<char> {
    if n == 0 { seq!['z', 'e', 'r', 'o'] }
    else if n == 1 { seq!['o', 'n', 'e'] }
    else if n == 2 { seq!['t', 'w', 'o'] }
    else if n == 3 { seq!['t', 'h', 'r', 'e', 'e'] }
    else if n == 4 { seq!['f', 'o', 'u', 'r'] }
    else if n == 5 { seq!['f', 'i', 'v', 'e'] }
    else if n == 6 { seq!['s', 'i', 'x'] }
    else if n == 7 { seq!['s', 'e', 'v', 'e', 'n'] }
    else if n == 8 { seq!['e', 'i', 'g', 'h', 't'] }
    else if n == 9 { seq!['n', 'i', 'n', 'e'] }
    else if n == 10 { seq!['t', 'e', 'n'] }
    else if n == 11 { seq!['e', 'l', 'e', 'v', 'e', 'n'] }
    else if n == 12 { seq!['t', 'w', 'e', 'l', 'v', 'e'] }
    else if n == 13 { seq!['t', 'h', 'i', 'r', 't', 'e', 'e', 'n'] }
    else if n == 14 { seq!['f', 'o', 'u', 'r', 't', 'e', 'e', 'n'] }
    else if n == 15 { seq!['f', 'i', 'f', 't', 'e', 'e', 'n'] }
    else if n == 16 { seq!['s', 'i', 'x', 't', 'e', 'e', 'n'] }
    else if n == 17 { seq!['s', 'e', 'v', 'e', 'n', 't', 'e', 'e', 'n'] }
    else if n == 18 { seq!['e', 'i', 'g', 'h', 't', 'e', 'e', 'n'] }
    else if n == 19 { seq!['n', 'i', 'n', 'e', 't', 'e', 'e', 'n'] }
    else if n == 20 { seq!['t', 'w', 'e', 'n', 't', 'y'] }
    else if n == 30 { seq!['t', 'h', 'i', 'r', 't', 'y'] }
    else if n == 40 { seq!['f', 'o', 'r', 't', 'y'] }
    else if n == 50 { seq!['f', 'i', 'f', 't', 'y'] }
    else if n == 60 { seq!['s', 'i', 'x', 't', 'y'] }
    else if n == 70 { seq!['s', 'e', 'v', 'e', 'n', 't', 'y'] }
    else if n == 80 { seq!['e', 'i', 'g', 'h', 't', 'y'] }
    else if n == 90 { seq!['n', 'i', 'n', 'e', 't', 'y'] }
    else if 21 <= n <= 29 { seq!['t', 'w', 'e', 'n', 't', 'y', '-'] + unit_word(n % 10) }
    else if 31 <= n <= 39 { seq!['t', 'h', 'i', 'r', 't', 'y', '-'] + unit_word(n % 10) }
    else if 41 <= n <= 49 { seq!['f', 'o', 'r', 't', 'y', '-'] + unit_word(n % 10) }
    else if 51 <= n <= 59 { seq!['f', 'i', 'f', 't', 'y', '-'] + unit_word(n % 10) }
    else if 61 <= n <= 69 { seq!['s', 'i', 'x', 't', 'y', '-'] + unit_word(n % 10) }
    else if 71 <= n <= 79 { seq!['s', 'e', 'v', 'e', 'n', 't', 'y', '-'] + unit_word(n % 10) }
    else if 81 <= n <= 89 { seq!['e', 'i', 'g', 'h', 't', 'y', '-'] + unit_word(n % 10) }
    else { seq!['n', 'i', 'n', 'e', 't', 'y', '-'] + unit_word(n % 10) }
}

spec fn is_valid_integer_string(s: Seq<char>) -> bool {
    (s.len() >= 1 && s.len() <= 3 && forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] && s[i] <= '9') ||
    (s.len() >= 2 && s.len() <= 4 && s[s.len() - 1] == '\n' && forall|i: int| 0 <= i < s.len() - 1 ==> '0' <= s[i] && s[i] <= '9')
}

spec fn parse_integer(s: Seq<char>) -> int {
    if s[s.len() - 1] == '\n' {
        parse_integer_helper(s.subrange(0, s.len() - 1))
    } else {
        parse_integer_helper(s)
    }
}

spec fn parse_integer_helper(s: Seq<char>) -> int {
    if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else if s.len() == 2 {
        10 * ((s[0] as int) - ('0' as int)) + ((s[1] as int) - ('0' as int))
    } else {
        100 * ((s[0] as int) - ('0' as int)) + 10 * ((s[1] as int) - ('0' as int)) + ((s[2] as int) - ('0' as int))
    }
}

spec fn unit_word(n: int) -> Seq<char> {
    if n == 1 { seq!['o', 'n', 'e'] }
    else if n == 2 { seq!['t', 'w', 'o'] }
    else if n == 3 { seq!['t', 'h', 'r', 'e', 'e'] }
    else if n == 4 { seq!['f', 'o', 'u', 'r'] }
    else if n == 5 { seq!['f', 'i', 'v', 'e'] }
    else if n == 6 { seq!['s', 'i', 'x'] }
    else if n == 7 { seq!['s', 'e', 'v', 'e', 'n'] }
    else if n == 8 { seq!['e', 'i', 'g', 'h', 't'] }
    else if n == 9 { seq!['n', 'i', 'n', 'e'] }
    else { seq![] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Avoided string concatenation to work around Verus internal error by building complete strings directly */
fn char_to_digit(c: char) -> (d: u8)
    requires
        '0' <= c,
        c <= '9',
    ensures
        d as int == (c as int) - ('0' as int),
        0 <= d <= 9,
{
    (c as u8) - ('0' as u8)
}

fn parse_int_exec(s: &str) -> (n: u32)
    requires
        s@.len() >= 1,
        s@.len() <= 3,
        forall|i: int| 0 <= i < s@.len() ==> '0' <= s@[i] && s@[i] <= '9',
    ensures
        n as int == parse_integer_helper(s@),
        0 <= n <= 999,
{
    let len = s.unicode_len();
    if len == 1 {
        let c0 = s.get_char(0);
        char_to_digit(c0) as u32
    } else if len == 2 {
        let c0 = s.get_char(0);
        let c1 = s.get_char(1);
        10 * (char_to_digit(c0) as u32) + (char_to_digit(c1) as u32)
    } else {
        let c0 = s.get_char(0);
        let c1 = s.get_char(1);
        let c2 = s.get_char(2);
        100 * (char_to_digit(c0) as u32) + 10 * (char_to_digit(c1) as u32) + (char_to_digit(c2) as u32)
    }
}

fn number_to_english(n: u32) -> (s: String)
    requires
        0 <= n <= 99,
    ensures
        s@ == correct_english_word(n as int),
{
    if n == 0 { String::from("zero") }
    else if n == 1 { String::from("one") }
    else if n == 2 { String::from("two") }
    else if n == 3 { String::from("three") }
    else if n == 4 { String::from("four") }
    else if n == 5 { String::from("five") }
    else if n == 6 { String::from("six") }
    else if n == 7 { String::from("seven") }
    else if n == 8 { String::from("eight") }
    else if n == 9 { String::from("nine") }
    else if n == 10 { String::from("ten") }
    else if n == 11 { String::from("eleven") }
    else if n == 12 { String::from("twelve") }
    else if n == 13 { String::from("thirteen") }
    else if n == 14 { String::from("fourteen") }
    else if n == 15 { String::from("fifteen") }
    else if n == 16 { String::from("sixteen") }
    else if n == 17 { String::from("seventeen") }
    else if n == 18 { String::from("eighteen") }
    else if n == 19 { String::from("nineteen") }
    else if n == 20 { String::from("twenty") }
    else if n == 21 { String::from("twenty-one") }
    else if n == 22 { String::from("twenty-two") }
    else if n == 23 { String::from("twenty-three") }
    else if n == 24 { String::from("twenty-four") }
    else if n == 25 { String::from("twenty-five") }
    else if n == 26 { String::from("twenty-six") }
    else if n == 27 { String::from("twenty-seven") }
    else if n == 28 { String::from("twenty-eight") }
    else if n == 29 { String::from("twenty-nine") }
    else if n == 30 { String::from("thirty") }
    else if n == 31 { String::from("thirty-one") }
    else if n == 32 { String::from("thirty-two") }
    else if n == 33 { String::from("thirty-three") }
    else if n == 34 { String::from("thirty-four") }
    else if n == 35 { String::from("thirty-five") }
    else if n == 36 { String::from("thirty-six") }
    else if n == 37 { String::from("thirty-seven") }
    else if n == 38 { String::from("thirty-eight") }
    else if n == 39 { String::from("thirty-nine") }
    else if n == 40 { String::from("forty") }
    else if n == 41 { String::from("forty-one") }
    else if n == 42 { String::from("forty-two") }
    else if n == 43 { String::from("forty-three") }
    else if n == 44 { String::from("forty-four") }
    else if n == 45 { String::from("forty-five") }
    else if n == 46 { String::from("forty-six") }
    else if n == 47 { String::from("forty-seven") }
    else if n == 48 { String::from("forty-eight") }
    else if n == 49 { String::from("forty-nine") }
    else if n == 50 { String::from("fifty") }
    else if n == 51 { String::from("fifty-one") }
    else if n == 52 { String::from("fifty-two") }
    else if n == 53 { String::from("fifty-three") }
    else if n == 54 { String::from("fifty-four") }
    else if n == 55 { String::from("fifty-five") }
    else if n == 56 { String::from("fifty-six") }
    else if n == 57 { String::from("fifty-seven") }
    else if n == 58 { String::from("fifty-eight") }
    else if n == 59 { String::from("fifty-nine") }
    else if n == 60 { String::from("sixty") }
    else if n == 61 { String::from("sixty-one") }
    else if n == 62 { String::from("sixty-two") }
    else if n == 63 { String::from("sixty-three") }
    else if n == 64 { String::from("sixty-four") }
    else if n == 65 { String::from("sixty-five") }
    else if n == 66 { String::from("sixty-six") }
    else if n == 67 { String::from("sixty-seven") }
    else if n == 68 { String::from("sixty-eight") }
    else if n == 69 { String::from("sixty-nine") }
    else if n == 70 { String::from("seventy") }
    else if n == 71 { String::from("seventy-one") }
    else if n == 72 { String::from("seventy-two") }
    else if n == 73 { String::from("seventy-three") }
    else if n == 74 { String::from("seventy-four") }
    else if n == 75 { String::from("seventy-five") }
    else if n == 76 { String::from("seventy-six") }
    else if n == 77 { String::from("seventy-seven") }
    else if n == 78 { String::from("seventy-eight") }
    else if n == 79 { String::from("seventy-nine") }
    else if n == 80 { String::from("eighty") }
    else if n == 81 { String::from("eighty-one") }
    else if n == 82 { String::from("eighty-two") }
    else if n == 83 { String::from("eighty-three") }
    else if n == 84 { String::from("eighty-four") }
    else if n == 85 { String::from("eighty-five") }
    else if n == 86 { String::from("eighty-six") }
    else if n == 87 { String::from("eighty-seven") }
    else if n == 88 { String::from("eighty-eight") }
    else if n == 89 { String::from("eighty-nine") }
    else if n == 90 { String::from("ninety") }
    else if n == 91 { String::from("ninety-one") }
    else if n == 92 { String::from("ninety-two") }
    else if n == 93 { String::from("ninety-three") }
    else if n == 94 { String::from("ninety-four") }
    else if n == 95 { String::from("ninety-five") }
    else if n == 96 { String::from("ninety-six") }
    else if n == 97 { String::from("ninety-seven") }
    else if n == 98 { String::from("ninety-eight") }
    else { String::from("ninety-nine") }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        stdin_input@.len() > 0,
        valid_input(stdin_input@),
    ensures 
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let n = parse_integer(stdin_input@);
            result@ == correct_english_word(n) + seq!['\n']
        }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified to avoid string concatenation issues */
    let len = stdin_input.unicode_len();
    let has_newline = stdin_input.get_char(len - 1) == '\n';
    
    let input_str = if has_newline {
        stdin_input.substring_char(0, len - 1)
    } else {
        stdin_input.clone()
    };
    
    let n = parse_int_exec(&input_str);
    
    let word = number_to_english(n);
    
    let mut result = word.clone();
    result.push_str("\n");
    result
}
// </vc-code>


}

fn main() {}