// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 1 &&
    is_valid_integer(lines[0]) &&
    {
        let t = string_to_int(lines[0]);
        t >= 0 &&
        lines.len() >= 1 + 2 * t &&
        forall|i: int| 0 <= i < t ==> {
            let line1_idx = 1 + 2 * i;
            let line2_idx = 1 + 2 * i + 1;
            line1_idx < lines.len() && line2_idx < lines.len() &&
            {
                let xy_parts = split_whitespace(lines[line1_idx]);
                let ab_parts = split_whitespace(lines[line2_idx]);
                xy_parts.len() >= 2 && ab_parts.len() >= 2 &&
                is_valid_integer(xy_parts[0]) &&
                is_valid_integer(xy_parts[1]) &&
                is_valid_integer(ab_parts[0]) &&
                is_valid_integer(ab_parts[1]) &&
                string_to_int(xy_parts[0]) >= 0 &&
                string_to_int(xy_parts[1]) >= 0 &&
                string_to_int(ab_parts[0]) >= 1 &&
                string_to_int(ab_parts[1]) >= 1
            }
        }
    }
}

spec fn valid_output(output: Seq<char>, input: Seq<char>) -> bool {
    let lines = split_lines(input);
    if lines.len() == 0 {
        output.len() == 0
    } else {
        let t = string_to_int(lines[0]);
        let output_lines = if output.len() == 0 { Seq::empty() } else { split_lines(output) };
        output_lines.len() == (if t == 0 { 0 } else { t }) &&
        forall|i: int| 0 <= i < output_lines.len() ==> is_valid_integer(output_lines[i])
    }
}

spec fn correct_computation(input: Seq<char>, output: Seq<char>) -> bool {
    let lines = split_lines(input);
    if lines.len() == 0 {
        output.len() == 0
    } else {
        let t = string_to_int(lines[0]);
        let output_lines = if output.len() == 0 { Seq::empty() } else { split_lines(output) };
        output_lines.len() == (if t == 0 { 0 } else { t }) &&
        forall|i: int| 0 <= i < t && 1 + 2 * i + 1 < lines.len() ==> {
            let xy_line = split_whitespace(lines[1 + 2 * i]);
            let ab_line = split_whitespace(lines[1 + 2 * i + 1]);
            (xy_line.len() >= 2 && ab_line.len() >= 2) ==> {
                let x = string_to_int(xy_line[0]);
                let y = string_to_int(xy_line[1]);
                let a = string_to_int(ab_line[0]);
                let b = string_to_int(ab_line[1]);
                let expected_result = if b <= 2 * a {
                    b * (if x <= y { x } else { y }) + (if x >= y { x } else { y } - if x <= y { x } else { y }) * a
                } else {
                    a * (x + y)
                };
                i < output_lines.len() && string_to_int(output_lines[i]) == expected_result
            }
        }
    }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 &&
    (s[0] == '-' ==> s.len() > 1) &&
    forall|i: int| (if s[0] == '-' { 1int } else { 0int }) <= i < s.len() ==> '0' <= s[i] <= '9'
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 {
        Seq::empty()
    } else {
        split_by_char(s, '\n')
    }
}

spec fn split_whitespace(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 {
        Seq::empty()
    } else {
        split_by_char(s, ' ')
    }
}

spec fn split_by_char(s: Seq<char>, delimiter: char) -> Seq<Seq<char>> {
    if s.len() == 0 {
        seq![Seq::empty()]
    } else if s[0] == delimiter {
        seq![Seq::empty()].add(split_by_char(s.subrange(1, s.len() as int), delimiter))
    } else {
        let rest = split_by_char(s.subrange(1, s.len() as int), delimiter);
        if rest.len() == 0 {
            seq![s]
        } else {
            seq![s.subrange(0, 1).add(rest[0])].add(rest.subrange(1, rest.len() as int))
        }
    }
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' && s.len() > 1 {
        -string_to_int_helper(s.subrange(1, s.len() as int))
    } else {
        string_to_int_helper(s)
    }
}

spec fn string_to_int_helper(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        if '0' <= s[0] <= '9' { s[0] as int - '0' as int } else { 0 }
    } else {
        string_to_int_helper(s.subrange(0, s.len() - 1)) * 10 +
        (if '0' <= s[s.len() - 1] <= '9' { s[s.len() - 1] as int - '0' as int } else { 0 })
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'].add(int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 {
        Seq::empty()
    } else {
        let digit_char = ((n % 10) + ('0' as int)) as char;
        int_to_string_helper(n / 10).push(digit_char)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (output: String)
    requires
        input@.len() > 0,
        valid_input(input@),
    ensures
        valid_output(output@, input@),
        correct_computation(input@, output@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}