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
/* helper modified by LLM (iteration 2): Renamed exec helper functions to avoid name conflicts with spec functions, changed return types to i64 for host arithmetic, and removed invalid 'as int' casts */
exec fn compute_single_area(coords: Vec<i64>) -> i64 {
    if coords.len() >= 4 {
        let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
        if computed >= 0 { computed } else { 0 }
    } else {
        0
    }
}

exec fn parse_int_pos(s: Vec<char>) -> i64
    decreases s.len()
{
    if s.is_empty() {
        0
    } else {
        let c = s[0];
        if c >= '0' && c <= '9' {
            (c as i64 - '0' as i64) + 10 * parse_int_pos(s.subrange(1, s.len()))
        } else {
            0
        }
    }
}

exec fn parse_int(s: Vec<char>) -> i64 {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        -parse_int_pos(s.subrange(1, s.len()))
    } else {
        parse_int_pos(s)
    }
}

exec fn parse_ints_helper_exec(s: Vec<char>, start: usize, pos: usize, acc: Vec<i64>) -> Vec<i64>
    decreases s.len() - pos
{
    if pos >= s.len() {
        if start < pos {
            let mut new_acc = acc;
            new_acc.push(parse_int(s.subrange(start, pos)));
            new_acc
        } else {
            acc
        }
    } else if s[pos] == ' ' {
        let mut new_acc = acc;
        if start < pos {
            new_acc.push(parse_int(s.subrange(start, pos)));
        }
        parse_ints_helper_exec(s, pos + 1, pos + 1, new_acc)
    } else {
        parse_ints_helper_exec(s, start, pos + 1, acc)
    }
}

exec fn parse_ints(s: Vec<char>) -> Vec<i64> {
    parse_ints_helper_exec(s, 0, 0, Vec::new())
}

exec fn int_to_string_pos(n: i64) -> Vec<char>
    decreases n when n > 0_i64
{
    if n < 10 {
        vec![(('0' as u32) + (n as u32)) as char]
    } else {
        let mut v = int_to_string_pos(n / 10);
        v.push((('0' as u32) + ((n % 10) as u32)) as char);
        v
    }
}

exec fn int_to_string(n: i64) -> Vec<char> {
    if n == 0 {
        vec!['0']
    } else if n > 0 {
        int_to_string_pos(n)
    } else {
        let mut v = vec!['-'];
        v.extend(int_to_string_pos(-n));
        v
    }
}

exec fn split_lines_helper_exec(s: Vec<char>, start: usize, pos: usize, acc: Vec<Vec<char>>) -> Vec<Vec<char>>
    decreases s.len() - pos
{
    if pos >= s.len() {
        if start < pos {
            let mut new_acc = acc;
            new_acc.push(s.subrange(start, pos));
            new_acc
        } else {
            acc
        }
    } else if s[pos] == '
' {
        let mut new_acc = acc;
        if start < pos {
            new_acc.push(s.subrange(start, pos));
        }
        split_lines_helper_exec(s, pos + 1, pos + 1, new_acc)
    } else {
        split_lines_helper_exec(s, start, pos + 1, acc)
    }
}

exec fn split_lines(s: Vec<char>) -> Vec<Vec<char>> {
    split_lines_helper_exec(s, 0, 0, Vec::new())
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
/* code modified by LLM (iteration 2): Updated variable types to match helper function signatures, fixed type casts and arithmetic for execution, and ensured proper indexing and accumulation */
{
    let processed_input = if input.len() > 0 && input[input.len() - 1] == '
' {
        input
    } else {
        let mut new_input = input;
        new_input.push('
');
        new_input
    };
    let lines = split_lines(processed_input);
    let total_area: i64 = if lines.len() == 0 {
        0
    } else {
        let n: i64 = parse_int(lines[0].clone());
        let mut i: usize = 0;
        let mut sum: i64 = 0;
        let num_lines = lines.len() - 1;
        let num_to_process: usize = if n >= 0 && (n as usize) <= num_lines {
            n as usize
        } else {
            num_lines
        };
        while i < num_to_process
            invariant
                i <= num_to_process,
                0 <= sum
        {
            let coords = parse_ints(lines[i + 1].clone());
            sum += compute_single_area(coords);
            i += 1;
        }
        sum
    };
    let mut result = int_to_string(total_area);
    result.push('
');
    result
}
// </vc-code>


}

fn main() {}