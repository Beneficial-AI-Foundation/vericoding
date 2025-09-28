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
/* helper modified by LLM (iteration 5): fixed illegal string slicing which caused a compilation error */
fn parse_int_from_str(s: &str) -> (ret: u64)
    requires
        valid_input(s@),
    ensures
        ret == parse_integer(s@),
{
    let bytes = s.as_bytes();
    let mut len = s.len();

    if len > 0 && bytes[len - 1] == b'\n' {
        len = len - 1;
    }

    if len == 1 {
        (bytes[0] - b'0') as u64
    } else if len == 2 {
        let d1 = (bytes[0] - b'0') as u64;
        let d2 = (bytes[1] - b'0') as u64;
        d1 * 10 + d2
    } else {
        let d1 = (bytes[0] - b'0') as u64;
        let d2 = (bytes[1] - b'0') as u64;
        let d3 = (bytes[2] - b'0') as u64;
        d1 * 100 + d2 * 10 + d3
    }
}

fn unit_to_word(n: u64) -> (s: String)
    requires 1 <= n <= 9,
    ensures s@ == unit_word(n as int),
{
    if n == 1 { String::from("one") }
    else if n == 2 { String::from("two") }
    else if n == 3 { String::from("three") }
    else if n == 4 { String::from("four") }
    else if n == 5 { String::from("five") }
    else if n == 6 { String::from("six") }
    else if n == 7 { String::from("seven") }
    else if n == 8 { String::from("eight") }
    else { String::from("nine") }
}

fn number_to_word(n: u64) -> (s: String)
    requires 0 <= n <= 99,
    ensures s@ == correct_english_word(n as int),
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
    else if n == 30 { String::from("thirty") }
    else if n == 40 { String::from("forty") }
    else if n == 50 { String::from("fifty") }
    else if n == 60 { String::from("sixty") }
    else if n == 70 { String::from("seventy") }
    else if n == 80 { String::from("eighty") }
    else if n == 90 { String::from("ninety") }
    else {
        let tens_digit = n / 10;
        let unit_digit = n % 10;

        let tens_str = if tens_digit == 2 { String::from("twenty") }
            else if tens_digit == 3 { String::from("thirty") }
            else if tens_digit == 4 { String::from("forty") }
            else if tens_digit == 5 { String::from("fifty") }
            else if tens_digit == 6 { String::from("sixty") }
            else if tens_digit == 7 { String::from("seventy") }
            else if tens_digit == 8 { String::from("eighty") }
            else { String::from("ninety") };

        let unit_str = unit_to_word(unit_digit);
        let mut res = tens_str;
        res.push_str("-");
        res.push_str(unit_str.as_str());
        res
    }
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
    /* code modified by LLM (iteration 5): no logic change needed here, fix was in helper */
    let n = parse_int_from_str(stdin_input);
    let mut word = number_to_word(n);
    word.push('\n');
    word
}

// </vc-code>


}

fn main() {}