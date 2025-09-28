// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
}

spec fn split_lines_func(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        split_lines_helper(s, 0, 0, seq![])
    }
}

spec fn split_lines_helper(s: Seq<char>, start: int, pos: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - pos when pos >= 0 && pos <= s.len()
{
    if pos >= s.len() {
        if start < pos {
            acc.push(s.subrange(start, pos))
        } else {
            acc
        }
    } else if s[pos] == '\n' {
        let new_acc = if start < pos {
            acc.push(s.subrange(start, pos))
        } else {
            acc
        };
        split_lines_helper(s, pos + 1, pos + 1, new_acc)
    } else {
        split_lines_helper(s, start, pos + 1, acc)
    }
}

spec fn parse_int_func(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        -parse_int_pos_func(s.subrange(1, s.len() as int))
    } else {
        parse_int_pos_func(s)
    }
}

spec fn parse_int_pos_func(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if '0' <= s[0] && s[0] <= '9' {
        (s[0] as int - '0' as int) + 10 * parse_int_pos_func(s.subrange(1, s.len() as int))
    } else {
        0
    }
}

spec fn parse_ints_func(s: Seq<char>) -> Seq<int> {
    if s.len() == 0 {
        seq![]
    } else {
        parse_ints_helper(s, 0, 0, seq![])
    }
}

spec fn parse_ints_helper(s: Seq<char>, start: int, pos: int, acc: Seq<int>) -> Seq<int>
    decreases s.len() - pos when pos >= 0 && pos <= s.len()
{
    if pos >= s.len() {
        if start < pos {
            acc.push(parse_int_func(s.subrange(start, pos)))
        } else {
            acc
        }
    } else if s[pos] == ' ' {
        let new_acc = if start < pos {
            acc.push(parse_int_func(s.subrange(start, pos)))
        } else {
            acc
        };
        parse_ints_helper(s, pos + 1, pos + 1, new_acc)
    } else {
        parse_ints_helper(s, start, pos + 1, acc)
    }
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n > 0 {
        int_to_string_pos(n)
    } else {
        seq!['-'] + int_to_string_pos(-n)
    }
}

spec fn int_to_string_pos(n: int) -> Seq<char>
    decreases n when n > 0
{
    if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string_pos(n / 10) + seq![('0' as int + (n % 10)) as char]
    }
}

spec fn compute_total_area(rectangle_lines: Seq<Seq<char>>) -> int
    decreases rectangle_lines.len()
{
    if rectangle_lines.len() == 0 {
        0
    } else {
        let coords = parse_ints_func(rectangle_lines[0]);
        let area = if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 { computed } else { 0 }
        } else {
            0
        };
        area + compute_total_area(rectangle_lines.subrange(1, rectangle_lines.len() as int))
    }
}

spec fn compute_total_area_partial(rectangle_lines: Seq<Seq<char>>, n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 || rectangle_lines.len() == 0 {
        0
    } else {
        let coords = parse_ints_func(rectangle_lines[0]);
        let area = if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 { computed } else { 0 }
        } else {
            0
        };
        area + compute_total_area_partial(rectangle_lines.subrange(1, rectangle_lines.len() as int), n - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error by adding comma in spec function */
proof fn compute_total_area_monotonic(rectangle_lines: Seq<Seq<char>>, n: int)
    requires n >= 0, n <= rectangle_lines.len()
    ensures compute_total_area_partial(rectangle_lines, n) <= compute_total_area(rectangle_lines)
    decreases n
{
    if n <= 0 {
    } else if rectangle_lines.len() == 0 {
    } else {
        compute_total_area_monotonic(rectangle_lines.subrange(1, rectangle_lines.len() as int), n - 1);
    }
}

proof fn split_lines_preserves_chars(s: Seq<char>)
    ensures split_lines_func(s).len() >= 0
{
}

proof fn lemma_parse_int_bounded(s: Seq<char>)
    ensures parse_int_func(s) >= -1000000 && parse_int_func(s) <= 1000000
{
}

proof fn lemma_area_nonnegative(coords: Seq<int>)
    requires coords.len() >= 4
    ensures (
        let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
        let area = if computed >= 0 { computed } else { 0 };
        area >= 0
    )
{
}

exec fn split_lines(input: &Vec<char>) -> Vec<Vec<char>> {
    let mut lines = Vec::new();
    let mut current_line = Vec::new();
    
    for i in 0..input.len() {
        if input[i] == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(input[i]);
        }
    }
    
    lines
}

exec fn parse_int(chars: &Vec<char>) -> int {
    if chars.len() == 0 {
        return 0;
    }
    
    let mut result = 0;
    let mut negative = false;
    let mut start = 0;
    
    if chars[0] == '-' {
        negative = true;
        start = 1;
    }
    
    for i in start..chars.len() {
        if chars[i] >= '0' && chars[i] <= '9' {
            result = result * 10 + (chars[i] as int - '0' as int);
        }
    }
    
    if negative { -result } else { result }
}

exec fn parse_ints(chars: &Vec<char>) -> Vec<int> {
    let mut result = Vec::new();
    let mut current_num = Vec::new();
    
    for i in 0..chars.len() {
        if chars[i] == ' ' {
            if current_num.len() > 0 {
                result.push(parse_int(&current_num));
                current_num = Vec::new();
            }
        } else {
            current_num.push(chars[i]);
        }
    }
    
    if current_num.len() > 0 {
        result.push(parse_int(&current_num));
    }
    
    result
}

exec fn compute_total_area_exec(lines: &[Vec<char>]) -> int {
    let mut total = 0;
    
    for i in 0..lines.len() {
        let coords = parse_ints(&lines[i]);
        if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            let area = if computed >= 0 { computed } else { 0 };
            total += area;
        }
    }
    
    total
}

exec fn compute_total_area_partial_exec(lines: &[Vec<char>], n: int) -> int {
    let mut total = 0;
    let limit = if n >= 0 && (n as usize) <= lines.len() { n as usize } else { lines.len() };
    
    for i in 0..limit {
        let coords = parse_ints(&lines[i]);
        if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            let area = if computed >= 0 { computed } else { 0 };
            total += area;
        }
    }
    
    total
}

exec fn int_to_string(n: int) -> Vec<char> {
    if n == 0 {
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    let mut num = n;
    let negative = num < 0;
    
    if negative {
        num = -num;
    }
    
    while num > 0 {
        result.push(('0' as int + (num % 10)) as char);
        num = num / 10;
    }
    
    if negative {
        result.push('-');
    }
    
    result.reverse();
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@),
    ensures 
        result@.len() >= 1,
        result@[result@.len() - 1] == '\n',
        exists|total_area: int| {
            &&& total_area >= 0
            &&& result@ == int_to_string_func(total_area) + seq!['\n']
            &&& {
                let processed_input = if input@.len() > 0 && input@[input@.len() - 1] == '\n' {
                    input@
                } else {
                    input@ + seq!['\n']
                };
                let lines = split_lines_func(processed_input);
                if lines.len() == 0 {
                    total_area == 0
                } else {
                    let n = parse_int_func(lines[0]);
                    if n >= 0 && n + 1 <= lines.len() {
                        total_area == compute_total_area(lines.subrange(1, n + 1))
                    } else {
                        total_area == compute_total_area_partial(lines.subrange(1, lines.len() as int), n)
                    }
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error in spec function calculation */
    let mut result = Vec::new();
    
    let processed_input: Vec<char> = if input.len() > 0 && input[input.len() - 1] == '\n' {
        input
    } else {
        let mut temp = input;
        temp.push('\n');
        temp
    };
    
    let lines = split_lines(&processed_input);
    
    let total_area = if lines.len() == 0 {
        0
    } else {
        let n = parse_int(&lines[0]);
        if n >= 0 && (n as usize) + 1 <= lines.len() {
            compute_total_area_exec(&lines[1..(n as usize) + 1])
        } else {
            compute_total_area_partial_exec(&lines[1..], n)
        }
    };
    
    let area_string = int_to_string(total_area);
    result.extend(area_string);
    result.push('\n');
    
    result
}
// </vc-code>


}

fn main() {}