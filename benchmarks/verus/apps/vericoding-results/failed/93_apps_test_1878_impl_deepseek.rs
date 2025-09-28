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

fn parse_int_impl(s: &Vec<char>) -> (result: int)
    requires valid_input(s@), ensures result == parse_int_func(s@),
{
    if s.is_empty() {
        0
    } else if s[0] == '-' {
        let pos_part = Vec::new();
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                pos_part@ == s@.subrange(1, i),
            decreases s.len() - i
        {
            pos_part.push(s[i]);
            i += 1;
        }
        -parse_int_pos_impl(&pos_part)
    } else {
        parse_int_pos_impl(s)
    }
}

fn parse_int_pos_impl(s: &Vec<char>) -> (result: int)
    requires valid_input(s@), ensures result == parse_int_pos_func(s@),
{
    if s.is_empty() {
        0
    } else {
        let digit_char = s[0];
        let digit_val = if '0' <= digit_char && digit_char <= '9' {
            digit_char as int - '0' as int
        } else {
            0
        };
        
        let rest = Vec::new();
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                rest@ == s@.subrange(1, i),
            decreases s.len() - i
        {
            rest.push(s[i]);
            i += 1;
        }
        
        digit_val + 10 * parse_int_pos_impl(&rest)
    }
}

fn parse_ints_impl(s: &Vec<char>) -> (result: Vec<int>)
    requires valid_input(s@), ensures result@ == parse_ints_func(s@),
{
    let mut result = Vec::new();
    let mut start = 0;
    let mut pos = 0;
    
    while pos <= s.len()
        invariant
            0 <= start <= pos <= s.len(),
            result@ == parse_ints_helper(s@, start, pos, seq![]),
        decreases s.len() - pos
    {
        if pos == s.len() {
            if start < pos {
                let num_str = Vec::new();
                let mut i = start;
                while i < pos
                    invariant
                        start <= i <= pos,
                        num_str@ == s@.subrange(start, i),
                    decreases pos - i
                {
                    num_str.push(s[i]);
                    i += 1;
                }
                let num = parse_int_impl(&num_str);
                result.push(num);
            }
            break;
        } else if s[pos] == ' ' {
            if start < pos {
                let num_str = Vec::new();
                let mut i = start;
                while i < pos
                    invariant
                        start <= i <= pos,
                        num_str@ == s@.subrange(start, i),
                    decreases pos - i
                {
                    num_str.push(s[i]);
                    i += 1;
                }
                let num = parse_int_impl(&num_str);
                result.push(num);
            }
            start = pos + 1;
            pos += 1;
        } else {
            pos += 1;
        }
    }
    
    result
}

fn split_lines_impl(s: &Vec<char>) -> (result: Vec<Vec<char>>)
    requires valid_input(s@), ensures result@ == split_lines_func(s@),
{
    let mut result = Vec::new();
    let mut start = 0;
    let mut pos = 0;
    
    while pos <= s.len()
        invariant
            0 <= start <= pos <= s.len(),
            result@ == split_lines_helper(s@, start, pos, seq![]),
        decreases s.len() - pos
    {
        if pos == s.len() {
            if start < pos {
                let line = Vec::new();
                let mut i = start;
                while i < pos
                    invariant
                        start <= i <= pos,
                        line@ == s@.subrange(start, i),
                    decreases pos - i
                {
                    line.push(s[i]);
                    i += 1;
                }
                result.push(line);
            }
            break;
        } else if s[pos] == '\n' {
            if start < pos {
                let line = Vec::new();
                let mut i = start;
                while i < pos
                    invariant
                        start <= i <= pos,
                        line@ == s@.subrange(start, i),
                    decreases pos - i
                {
                    line.push(s[i]);
                    i += 1;
                }
                result.push(line);
            }
            start = pos + 1;
            pos += 1;
        } else {
            pos += 1;
        }
    }
    
    result
}

fn int_to_string_impl(n: int) -> (result: Vec<char>)
    ensures result@ == int_to_string_func(n),
{
    if n == 0 {
        vec!['0']
    } else if n > 0 {
        int_to_string_pos_impl(n)
    } else {
        let mut result = vec!['-'];
        let pos_str = int_to_string_pos_impl(-n);
        result.extend(pos_str);
        result
    }
}

fn int_to_string_pos_impl(n: int) -> (result: Vec<char>)
    requires n > 0, ensures result@ == int_to_string_pos(n),
{
    if n < 10 {
        vec![('0' as int + n) as char]
    } else {
        let digit = n % 10;
        let rest = n / 10;
        let mut result = int_to_string_pos_impl(rest);
        result.push(('0' as int + digit) as char);
        result
    }
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
    let processed_input = if !input.is_empty() && input.last() == Some(&'\n') {
        input
    } else {
        let mut new_input = input.clone();
        new_input.push('\n');
        new_input
    };
    
    let lines = split_lines_impl(&processed_input);
    
    if lines.is_empty() {
        let result = int_to_string_impl(0);
        let mut final_result = result;
        final_result.push('\n');
        final_result
    } else {
        let n_line = &lines[0];
        let n = parse_int_impl(n_line);
        
        let total_area = if n >= 0 && (n as usize) + 1 <= lines.len() {
            compute_total_area_calc(&lines, 1, n as usize)
        } else {
            compute_total_area_partial_calc(&lines, 1, n)
        };
        
        let result = int_to_string_impl(total_area);
        let mut final_result = result;
        final_result.push('\n');
        final_result
    }
}

fn compute_total_area_calc(lines: &Vec<Vec<char>>, start_index: usize, count: usize) -> (result: int)
    requires 
        start_index <= lines.len(),
        start_index + count <= lines.len(),
    ensures result == compute_total_area(lines@.subrange(start_index as int, (start_index + count) as int)),
{
    let mut total = 0;
    let mut i = start_index;
    while i < start_index + count
        invariant
            i >= start_index <= start_index + count,
            total == compute_total_area(lines@.subrange(start_index as int, i as int)),
        decreases (start_index + count) - i
    {
        let coords = parse_ints_impl(&lines[i]);
        let area = if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 { computed } else { 0 }
        } else {
            0
        };
        total += area;
        i += 1;
    }
    total
}

fn compute_total_area_partial_calc(lines: &Vec<Vec<char>>, start_index: usize, count: int) -> (result: int)
    requires 
        start_index <= lines.len(),
    ensures result == compute_total_area_partial(lines@.subrange(start_index as int, lines.len() as int), count),
{
    if count <= 0 || start_index >= lines.len() {
        0
    } else {
        let coords = parse_ints_impl(&lines[start_index]);
        let area = if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 { computed } else { 0 }
        } else {
            0
        };
        area + compute_total_area_partial_calc(lines, start_index + 1, count - 1)
    }
}
// </vc-code>


}

fn main() {}