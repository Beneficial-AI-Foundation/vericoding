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
/* helper modified by LLM (iteration 5): parse input string to runtime i32 and connect to spec */
fn parse_integer_runtime(s: &str) -> (result: i32)
    requires
        valid_input(s@),
    ensures
        (result as int) == parse_integer(s@),
{
    let b = s.as_bytes();
    let len_usize = b.len();
    let end: usize = if len_usize > 0 && b[len_usize - 1] == b'\n' { len_usize - 1 } else { len_usize };
    let mut res: i32 = 0;
    let mut i: usize = 0;
    while i < end
        invariant
            i <= end,
        decreases
            end - i
    {
        let digit = (b[i] - b'0') as i32;
        res = res * 10 + digit;
        i += 1;
    }
    proof {
        let s_seq = s@;
        let end_i: int = if s_seq[s_seq.len() - 1] == '\n' { s_seq.len() - 1 } else { s_seq.len() };
        if end_i == 1 {
            let d0 = (b[0] as int) - (b'0' as int);
            assert((res as int) == d0);
            assert((res as int) == parse_integer_helper(s_seq.subrange(0, 1)));
            assert((res as int) == parse_integer(s_seq));
        } else if end_i == 2 {
            let d0 = (b[0] as int) - (b'0' as int);
            let d1 = (b[1] as int) - (b'0' as int);
            assert((res as int) == 10 * d0 + d1);
            assert((res as int) == parse_integer_helper(s_seq.subrange(0, 2)));
            assert((res as int) == parse_integer(s_seq));
        } else {
            let d0 = (b[0] as int) - (b'0' as int);
            let d1 = (b[1] as int) - (b'0' as int);
            let d2 = (b[2] as int) - (b'0' as int);
            assert((res as int) == 100 * d0 + 10 * d1 + d2);
            assert((res as int) == parse_integer_helper(s_seq.subrange(0, 3)));
            assert((res as int) == parse_integer(s_seq));
        }
    }
    result = res;
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
/* code modified by LLM (iteration 5): build english word from parsed integer and prove relation to spec */
{
    let n = parse_integer_runtime(stdin_input);

    let mut out = String::new();

    if n == 0 {
        out.push_str("zero");
    } else if n == 1 {
        out.push_str("one");
    } else if n == 2 {
        out.push_str("two");
    } else if n == 3 {
        out.push_str("three");
    } else if n == 4 {
        out.push_str("four");
    } else if n == 5 {
        out.push_str("five");
    } else if n == 6 {
        out.push_str("six");
    } else if n == 7 {
        out.push_str("seven");
    } else if n == 8 {
        out.push_str("eight");
    } else if n == 9 {
        out.push_str("nine");
    } else if n == 10 {
        out.push_str("ten");
    } else if n == 11 {
        out.push_str("eleven");
    } else if n == 12 {
        out.push_str("twelve");
    } else if n == 13 {
        out.push_str("thirteen");
    } else if n == 14 {
        out.push_str("fourteen");
    } else if n == 15 {
        out.push_str("fifteen");
    } else if n == 16 {
        out.push_str("sixteen");
    } else if n == 17 {
        out.push_str("seventeen");
    } else if n == 18 {
        out.push_str("eighteen");
    } else if n == 19 {
        out.push_str("nineteen");
    } else {
        let tens = match n / 10 {
            2 => "twenty",
            3 => "thirty",
            4 => "forty",
            5 => "fifty",
            6 => "sixty",
            7 => "seventy",
            8 => "eighty",
            9 => "ninety",
            _ => "",
        };
        out.push_str(tens);
        let u = n % 10;
        if u != 0 {
            out.push('-');
            out.push_str(match u {
                1 => "one",
                2 => "two",
                3 => "three",
                4 => "four",
                5 => "five",
                6 => "six",
                7 => "seven",
                8 => "eight",
                9 => "nine",
                _ => "",
            });
        }
    }

    out.push('\n');

    result = out;
    proof {
        let n_spec = parse_integer(stdin_input@);
        assert((n as int) == n_spec);

        if n_spec == 0 {
            assert(result@ == correct_english_word(0) + seq!['\n']);
        } else if n_spec == 1 {
            assert(result@ == correct_english_word(1) + seq!['\n']);
        } else if n_spec == 2 {
            assert(result@ == correct_english_word(2) + seq!['\n']);
        } else if n_spec == 3 {
            assert(result@ == correct_english_word(3) + seq!['\n']);
        } else if n_spec == 4 {
            assert(result@ == correct_english_word(4) + seq!['\n']);
        } else if n_spec == 5 {
            assert(result@ == correct_english_word(5) + seq!['\n']);
        } else if n_spec == 6 {
            assert(result@ == correct_english_word(6) + seq!['\n']);
        } else if n_spec == 7 {
            assert(result@ == correct_english_word(7) + seq!['\n']);
        } else if n_spec == 8 {
            assert(result@ == correct_english_word(8) + seq!['\n']);
        } else if n_spec == 9 {
            assert(result@ == correct_english_word(9) + seq!['\n']);
        } else if n_spec == 10 {
            assert(result@ == correct_english_word(10) + seq!['\n']);
        } else if n_spec == 11 {
            assert(result@ == correct_english_word(11) + seq!['\n']);
        } else if n_spec == 12 {
            assert(result@ == correct_english_word(12) + seq!['\n']);
        } else if n_spec == 13 {
            assert(result@ == correct_english_word(13) + seq!['\n']);
        } else if n_spec == 14 {
            assert(result@ == correct_english_word(14) + seq!['\n']);
        } else if n_spec == 15 {
            assert(result@ == correct_english_word(15) + seq!['\n']);
        } else if n_spec == 16 {
            assert(result@ == correct_english_word(16) + seq!['\n']);
        } else if n_spec == 17 {
            assert(result@ == correct_english_word(17) + seq!['\n']);
        } else if n_spec == 18 {
            assert(result@ == correct_english_word(18) + seq!['\n']);
        } else if n_spec == 19 {
            assert(result@ == correct_english_word(19) + seq!['\n']);
        } else {
            let ten = n_spec / 10;
            let base = if ten == 2 { seq!['t','w','e','n','t','y'] }
                       else if ten == 3 { seq!['t','h','i','r','t','y'] }
                       else if ten == 4 { seq!['f','o','r','t','y'] }
                       else if ten == 5 { seq!['f','i','f','t','y'] }
                       else if ten == 6 { seq!['s','i','x','t','y'] }
                       else if ten == 7 { seq!['s','e','v','e','n','t','y'] }
                       else if ten == 8 { seq!['e','i','g','h','t','y'] }
                       else { seq!['n','i','n','e','t','y'] };
            let u = n_spec % 10;
            if u == 0 {
                assert(result@ == base + seq!['\n']);
            } else {
                assert(result@ == base + seq!['-'] + unit_word(u) + seq!['\n']);
            }
        }
    }

    result
}

// </vc-code>


}

fn main() {}