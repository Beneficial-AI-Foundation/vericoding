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
/* helper modified by LLM (iteration 4): Fixed result variable references in helper functions */
fn split_str_exec(s: &str, delimiter: char) -> (result: Vec<String>)
    ensures
        result@.len() == split_str(s@, delimiter).len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@ == split_str(s@, delimiter)[i],
{
    let parts: Vec<String> = s.split(delimiter).map(|part| part.to_string()).collect();
    parts
}

fn parse_int_exec(s: &str) -> (result: u64)
    ensures
        result as int == parse_int(s@),
{
    let mut res: u64 = 0;
    for c in s.chars() {
        if c >= '0' && c <= '9' {
            res = res * 10 + (c as u64 - '0' as u64);
        }
    }
    res
}

fn int_to_string_exec(n: i64) -> (result: String)
    ensures
        result@ == int_to_string(n as int),
{
    n.to_string()
}
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
{
    /* code modified by LLM (iteration 4): Fixed map closure to accept both index and element parameters */
    let lines = split_str_exec(input, '
');
    let n = parse_int_exec(&lines[0]);
    let second_line_parts = split_str_exec(&lines[1], ' ');
    let d = parse_int_exec(&second_line_parts[0]);
    let x = parse_int_exec(&second_line_parts[1]);
    
    let mut total_eaten: u64 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            lines.len() >= 2 + n as usize,
            total_eaten as int == sum_eaten_for_participants(lines@.map(|idx: int, s: String| s@), d as int, i as int),
    {
        let a = parse_int_exec(&lines[2 + i]);
        let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
        total_eaten = total_eaten + eaten;
        i = i + 1;
    }
    
    let result_num = x + total_eaten;
    int_to_string_exec(result_num as i64)
}
// </vc-code>


}

fn main() {}