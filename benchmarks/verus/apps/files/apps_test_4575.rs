// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(input: &str) -> bool {
    let lines = split(input, '\n');
    lines.len() >= 2 &&
    parse_int(&lines[0]) >= 1 && {
        let n = parse_int(&lines[0]);
        let second_line_parts = split(&lines[1], ' ');
        second_line_parts.len() >= 2 &&
        parse_int(&second_line_parts[0]) >= 1 &&
        parse_int(&second_line_parts[1]) >= 0 &&
        lines.len() >= 2 + n &&
        forall|i: int| 0 <= i < n ==> parse_int(&lines[2 + i]) >= 1
    }
}

spec fn compute_expected_result(input: &str) -> String
    requires valid_input(input)
{
    let lines = split(input, '\n');
    let n = parse_int(&lines[0]);
    let second_line_parts = split(&lines[1], ' ');
    let d = parse_int(&second_line_parts[0]);
    let x = parse_int(&second_line_parts[1]);
    let total_eaten = sum_eaten_for_participants(&lines, d, n);
    int_to_string(x + total_eaten)
}

spec fn sum_eaten_for_participants(lines: &Seq<String>, d: int, count: int) -> int
    requires 
        lines.len() >= 2 + count &&
        d >= 1 &&
        count >= 0
    decreases count
{
    if count == 0 {
        0
    } else {
        let a = parse_int(&lines[2 + count - 1]);
        let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
        eaten + sum_eaten_for_participants(lines, d, count - 1)
    }
}

spec fn split(s: &str, delimiter: char) -> Seq<String> {
    if s.len() == 0 {
        seq![]
    } else {
        split_helper(s, delimiter, 0, 0, seq![])
    }
}

spec fn split_helper(s: &str, delimiter: char, start: int, current: int, acc: Seq<String>) -> Seq<String>
    requires 0 <= start <= current <= s.len()
    decreases s.len() - current
{
    if current == s.len() {
        if start == current {
            acc
        } else {
            acc.push(s.view().subrange(start, current).to_string())
        }
    } else if s.get_char(current as usize) == delimiter {
        split_helper(s, delimiter, current + 1, current + 1, acc.push(s.view().subrange(start, current).to_string()))
    } else {
        split_helper(s, delimiter, start, current + 1, acc)
    }
}

spec fn parse_int(s: &str) -> int {
    if s.len() == 0 {
        0
    } else {
        parse_int_helper(s, 0, 0)
    }
}

spec fn parse_int_helper(s: &str, index: int, acc: int) -> int
    requires 0 <= index <= s.len()
    decreases s.len() - index
{
    if index == s.len() {
        acc
    } else if '0' <= s.get_char(index as usize) && s.get_char(index as usize) <= '9' {
        parse_int_helper(s, index + 1, acc * 10 + (s.get_char(index as usize) as int - '0' as int))
    } else {
        acc
    }
}

spec fn int_to_string(n: int) -> String {
    if n == 0 {
        "0".to_string()
    } else if n < 0 {
        "-".to_string() + int_to_string_helper(-n)
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> String
    requires n > 0
    decreases n
{
    if n < 10 {
        String::from_char((n + '0' as int) as char)
    } else {
        int_to_string_helper(n / 10) + String::from_char((n % 10 + '0' as int) as char)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires 
        input.len() > 0 &&
        valid_input(input)
    ensures 
        result.len() > 0 &&
        result == compute_expected_result(input)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "".to_string()
    // impl-end
}
// </vc-code>


}

fn main() {}