// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_str(input, '\n');
    lines.len() >= 2 &&
    parse_int(lines[0]) >= 1 &&
    {
        let n = parse_int(lines[0]);
        let second_line_parts = split_str(lines[1], ' ');
        second_line_parts.len() >= 2 &&
        parse_int(second_line_parts[0]) >= 1 &&
        parse_int(second_line_parts[1]) >= 0 &&
        lines.len() >= 2 + n &&
        forall|i: int| 0 <= i < n ==> #[trigger] parse_int(lines[2 + i]) >= 1
    }
}

spec fn compute_expected_result(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let lines = split_str(input, '\n');
    let n = parse_int(lines[0]);
    let second_line_parts = split_str(lines[1], ' ');
    let d = parse_int(second_line_parts[0]);
    let x = parse_int(second_line_parts[1]);
    let total_eaten = sum_eaten_for_participants(lines, d, n);
    int_to_string(x + total_eaten)
}

spec fn sum_eaten_for_participants(lines: Seq<Seq<char>>, d: int, count: int) -> int 
    recommends lines.len() >= 2 + count && d >= 1 && count >= 0
    decreases count
    when count >= 0
{
    if count == 0 {
        0
    } else {
        let a = parse_int(lines[2 + count - 1]);
        let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
        eaten + sum_eaten_for_participants(lines, d, count - 1)
    }
}

spec fn split_str(s: Seq<char>, delimiter: char) -> Seq<Seq<char>> {
    if s.len() == 0 {
        seq![]
    } else {
        split_helper(s, delimiter, 0, 0, seq![])
    }
}

spec fn split_helper(s: Seq<char>, delimiter: char, start: int, current: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    recommends 0 <= start <= current <= s.len()
    decreases s.len() - current
    when 0 <= current <= s.len()
{
    if current == s.len() {
        if start == current {
            acc
        } else {
            acc.push(s.subrange(start, current))
        }
    } else if s[current] == delimiter {
        split_helper(s, delimiter, current + 1, current + 1, acc.push(s.subrange(start, current)))
    } else {
        split_helper(s, delimiter, start, current + 1, acc)
    }
}

spec fn parse_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else {
        parse_int_helper(s, 0, 0)
    }
}

spec fn parse_int_helper(s: Seq<char>, index: int, acc: int) -> int
    recommends 0 <= index <= s.len()
    decreases s.len() - index
    when 0 <= index <= s.len()
{
    if index == s.len() {
        acc
    } else if '0' <= s[index] <= '9' {
        parse_int_helper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    } else {
        acc
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'] + int_to_string_helper(-n)
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n > 0
    decreases n
    when n > 0
{
    if n < 10 {
        seq![(n + '0' as int) as char]
    } else {
        int_to_string_helper(n / 10) + seq![(n % 10 + '0' as int) as char]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [reverted changes] */
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires
        input@.len() > 0,
        valid_input(input@),
    ensures
        result@.len() > 0,
        result@ == compute_expected_result(input@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed variable name from `x_str` to the correct `second_line_parts.vget(1)` to access the second part of the string, also changed into_seq() to into() to resolve compilation errors and fixed type mismatches */
{
    let lines = input.into().split_by_char('\n');
    let n_str = &lines.vget(0);
    let n = parse_int(n_str.into());

    let second_line = &lines.vget(1);
    let second_line_parts = second_line.into().split_by_char(' ');
    let d_str = &second_line_parts.vget(0);
    let d: int = parse_int(d_str.into());
    let x: int = parse_int(second_line_parts.vget(1).into());

    let mut total_eaten: int = 0;
    let mut i: int = 0;

    while i < n
        invariant
            0 <= i <= n,
            total_eaten == sum_eaten_for_participants(lines.map(|s: &str| s.into()), d, i),
            lines.len() >= 2 + n,
            d >= 1,
        decreases n - i
    {
        let line_i = &lines.vget(2 + i);
        let a: int = parse_int(line_i.into());

        if a > 0 {
            let eaten = (d + a - 1) / a;
            total_eaten = total_eaten + eaten;
        }

        i = i + 1;
    }
    
    (x + total_eaten).to_string()
}
// </vc-code>


}

fn main() {}