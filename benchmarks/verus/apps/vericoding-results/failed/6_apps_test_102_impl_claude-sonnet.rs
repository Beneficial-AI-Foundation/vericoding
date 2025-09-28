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
/* helper modified by LLM (iteration 5): removed unsupported trim() method and implemented direct parsing */
fn parse_string_to_int(s: &str) -> (result: usize)
    requires
        s@.len() > 0,
        valid_input(s@),
    ensures
        result == parse_integer(s@),
{
    let bytes = s.as_bytes();
    let mut result = 0;
    let mut i = 0;
    while i < bytes.len() && bytes[i] != b'\n'
        invariant
            0 <= i <= bytes.len(),
            result == parse_integer_helper(s@.subrange(0, i as int)),
        decreases bytes.len() - i
    {
        let digit = (bytes[i] - b'0') as usize;
        result = result * 10 + digit;
        i += 1;
    }
    result
}

fn convert_to_english(n: usize) -> (result: String)
    requires
        0 <= n <= 99,
    ensures
        result@ == correct_english_word(n as int),
{
    if n == 0 { "zero".to_string() }
    else if n == 1 { "one".to_string() }
    else if n == 2 { "two".to_string() }
    else if n == 3 { "three".to_string() }
    else if n == 4 { "four".to_string() }
    else if n == 5 { "five".to_string() }
    else if n == 6 { "six".to_string() }
    else if n == 7 { "seven".to_string() }
    else if n == 8 { "eight".to_string() }
    else if n == 9 { "nine".to_string() }
    else if n == 10 { "ten".to_string() }
    else if n == 11 { "eleven".to_string() }
    else if n == 12 { "twelve".to_string() }
    else if n == 13 { "thirteen".to_string() }
    else if n == 14 { "fourteen".to_string() }
    else if n == 15 { "fifteen".to_string() }
    else if n == 16 { "sixteen".to_string() }
    else if n == 17 { "seventeen".to_string() }
    else if n == 18 { "eighteen".to_string() }
    else if n == 19 { "nineteen".to_string() }
    else if n == 20 { "twenty".to_string() }
    else if n == 30 { "thirty".to_string() }
    else if n == 40 { "forty".to_string() }
    else if n == 50 { "fifty".to_string() }
    else if n == 60 { "sixty".to_string() }
    else if n == 70 { "seventy".to_string() }
    else if n == 80 { "eighty".to_string() }
    else if n == 90 { "ninety".to_string() }
    else {
        let tens = n / 10;
        let ones = n % 10;
        let tens_word = if tens == 2 { "twenty" }
                       else if tens == 3 { "thirty" }
                       else if tens == 4 { "forty" }
                       else if tens == 5 { "fifty" }
                       else if tens == 6 { "sixty" }
                       else if tens == 7 { "seventy" }
                       else if tens == 8 { "eighty" }
                       else { "ninety" };
        let ones_word = if ones == 1 { "one" }
                       else if ones == 2 { "two" }
                       else if ones == 3 { "three" }
                       else if ones == 4 { "four" }
                       else if ones == 5 { "five" }
                       else if ones == 6 { "six" }
                       else if ones == 7 { "seven" }
                       else if ones == 8 { "eight" }
                       else { "nine" };
        format!("{}-{}", tens_word, ones_word)
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
    /* code modified by LLM (iteration 5): using helper functions to parse input and convert to English */
    let n = parse_string_to_int(stdin_input);
    let english_word = convert_to_english(n);
    format!("{}\n", english_word)
}
// </vc-code>


}

fn main() {}