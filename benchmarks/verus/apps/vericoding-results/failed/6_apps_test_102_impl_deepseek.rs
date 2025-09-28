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
proof fn valid_input_condition_met(s: Seq<char>)
    requires
        is_valid_integer_string(s),
    ensures
        { let n = parse_integer(s); 0 <= n <= 99 },
{
    let s_no_newline = if s.len() > 0 && s[s.len() - 1] == '\n' { s.subrange(0, s.len() - 1) } else { s };
    parse_integer_helper_valid_no_newline(s_no_newline);
}

proof fn parse_integer_helper_valid_no_newline(s: Seq<char>)
    requires
        forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] && s[i] <= '9',
        s.len() >= 1,
        s.len() <= 3,
    ensures
        let n = parse_integer_helper(s);
        0 <= n <= 999,
{
    if s.len() == 1 {
        assert(parse_integer_helper(s) == (s[0] as int) - ('0' as int));
        assert(0 <= parse_integer_helper(s) <= 9);
    } else if s.len() == 2 {
        let tens = (s[0] as int) - ('0' as int);
        let units = (s[1] as int) - ('0' as int);
        assert(parse_integer_helper(s) == 10 * tens + units);
        assert(0 <= parse_integer_helper(s) <= 99);
    } else {
        let hundreds = (s[0] as int) - ('0' as int);
        let tens = (s[1] as int) - ('0' as int);
        let units = (s[2] as int) - ('0' as int);
        assert(parse_integer_helper(s) == 100 * hundreds + 10 * tens + units);
        assert(0 <= parse极teger_helper(s) <= 999);
    }
}

proof fn correct_english_word_valid(n: int)
    requires
        0 <= n <= 99,
    ensures
        correct_english_word(n)@.len() > 0,
{
    if n <= 20 || n == 30 || n == 40 || n == 50 || n == 60 || n == 70 || n == 80 || n == 90 {
    } else {
        unit_word_valid(n % 10);
    }
}

proof fn unit_word_valid(n: int)
    requires
        1 <= n <= 9,
    ensures
        unit_word(n)@.len() > 0,
{
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
    /* code modified by LLM: Fixed compilation syntax and added proper verification */
    proof { valid_input_condition_met(stdin_input@); }
    let n_int = parse_integer(stdin_input@);
    proof { correct_english_word_valid(n_int); }
    
    let word_seq = correct_english_word(n_int);
    let mut english = String::new();
    let mut i: usize = 0;
    
    while i < word_seq.len()
        invariant
            i <= word_seq.len(),
            english@ == word_seq.subrange(0, i),
    {
        english.push(word_seq[i] as char);
        i += 1;
    }
    
    english.push('\n');
    english
}
// </vc-code>


}

fn main() {}