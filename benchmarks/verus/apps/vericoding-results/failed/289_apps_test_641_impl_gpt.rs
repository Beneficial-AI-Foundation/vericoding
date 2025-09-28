// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_on_space(s: Seq<char>) -> Seq<Seq<char>>;

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    ({
        let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
        let parts = split_on_space(trimmed);
        parts.len() >= 1
    })
}

spec fn get_expected_result(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let trimmed = if input.len() > 0 && input[input.len() as int - 1] == '\n' { input.subrange(0, input.len() as int - 1) } else { input };
    let parts = split_on_space(trimmed);
    if parts[parts.len() as int - 1] == seq!['m', 'o', 'n', 't', 'h'] {
        if parts[0] == seq!['3', '1'] { seq!['7', '\n'] }
        else if parts[0] == seq!['3', '0'] { seq!['1', '1', '\n'] }
        else { seq!['1', '2', '\n'] }
    } else {
        if parts[0] == seq!['5'] || parts[0] == seq!['6'] { seq!['5', '3', '\n'] }
        else { seq!['5', '2', '\n'] }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple digit predicate kept for potential reasoning; no side effects */
spec fn is_digit(c: char) -> bool { '0' <= c && c <= '9' }
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures result@ == get_expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid &str slicing by operating on &[u8] tokens; compare to byte literals */
    let bytes = input.as_bytes();
    let n_input = bytes.len();
    let trimmed_len = if n_input > 0 && bytes[n_input - 1] == b'\n' { n_input - 1 } else { n_input };

    let mut first: Option<&[u8]> = None;
    let mut last: &[u8] = &[];

    let mut start: usize = 0;
    let mut i: usize = 0;
    while i < trimmed_len {
        if bytes[i] == b' ' {
            let tok: &[u8] = &bytes[start..i];
            if first.is_none() {
                first = Some(tok);
            }
            last = tok;
            start = i + 1;
        }
        i += 1;
    }
    let tok: &[u8] = &bytes[start..trimmed_len];
    if first.is_none() {
        first = Some(tok);
    }
    last = tok;

    let f: &[u8] = match first {
        Some(x) => x,
        None => &[],
    };

    let mut out = String::new();
    if last == b"month" {
        if f == b"31" {
            out.push('7');
            out.push('\n');
        } else if f == b"30" {
            out.push('1');
            out.push('1');
            out.push('\n');
        } else {
            out.push('1');
            out.push('2');
            out.push('\n');
        }
    } else {
        if f == b"5" || f == b"6" {
            out.push('5');
            out.push('3');
            out.push('\n');
        } else {
            out.push('5');
            out.push('2');
            out.push('\n');
        }
    }

    out
}
// </vc-code>


}

fn main() {}