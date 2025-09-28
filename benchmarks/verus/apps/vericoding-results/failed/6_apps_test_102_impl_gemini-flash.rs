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
/* helper modified by LLM (iteration 4): This section is intentionally left blank as no helper modifications are needed. */
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
    /* code modified by LLM (iteration 4): Corrected type casting from `usize` to `int` for sequence indexing. */
    let input_vec_char = stdin_input.chars().collect::<Vec<char>>();
    let input_seq = input_vec_char@;

    let n = parse_integer(input_seq);

    let word_seq = correct_english_word(n);
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < word_seq.len()
        invariant
            0 <= i as int <= word_seq.len(),
            result_vec@ == word_seq.subrange(0, i as int),
        decreases word_seq.len() - i as int
    {
        result_vec.push(word_seq.index(i as nat));
        i = i + 1;
    }
    result_vec.push('\n');

    // Convert Vec<char> to String manually
    let mut result_string_vec: Vec<char> = Vec::new();
    let mut j: usize = 0;
    while j < result_vec.len()
        invariant
            0 <= j as int <= result_vec.len(),
            result_string_vec@ == result_vec@.subrange(0, j as int),
        decreases result_vec.len() - j as int
    {
        result_string_vec.push(result_vec.index(j as nat));
        j = j + 1;
    }
    String::from_iter(result_string_vec)
}
// </vc-code>


}

fn main() {}