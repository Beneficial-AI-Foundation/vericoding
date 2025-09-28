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
/* helper modified by LLM (iteration 5): convert int to Vec<char> */
fn int_to_vec(n: int) -> Vec<char>
    ensures
        result@ == int_to_string_func(n),
{
    let s = int_to_string_func(n);
    let mut v: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            v@ == s.subrange(0, i),
        decreases s.len() - i
    {
        v.push(s@[i]);
        i = i + 1;
    }
    v
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
    /* code modified by LLM (iteration 5): prepare input, compute total_area in ghost, convert to Vec and append newline */
    let mut input_runtime = input.clone();
    if input_runtime.len() == 0 || input_runtime[input_runtime.len() - 1] != '\n' {
        input_runtime.push('\n');
    }

    ghost {
        let processed_spec: Seq<char> = if input@.len() > 0 && input@[input@.len() - 1] == '\n' {
            input@
        } else {
            input@ + seq!['\n']
        };

        let lines_spec: Seq<Seq<char>> = split_lines_func(processed_spec);

        let _total_area: int = if lines_spec.len() == 0 {
            0
        } else {
            let n = parse_int_func(lines_spec[0]);
            if n >= 0 && n + 1 <= lines_spec.len() {
                compute_total_area(lines_spec.subrange(1, n + 1))
            } else {
                compute_total_area_partial(lines_spec.subrange(1, lines_spec.len() as int), n)
            }
        };
    }

    ghost let total_area_val: int = {
        let processed_spec: Seq<char> = if input@.len() > 0 && input@[input@.len() - 1] == '\n' {
            input@
        } else {
            input@ + seq!['\n']
        };
        let lines_spec: Seq<Seq<char>> = split_lines_func(processed_spec);
        if lines_spec.len() == 0 {
            0
        } else {
            let n = parse_int_func(lines_spec[0]);
            if n >= 0 && n + 1 <= lines_spec.len() {
                compute_total_area(lines_spec.subrange(1, n + 1))
            } else {
                compute_total_area_partial(lines_spec.subrange(1, lines_spec.len() as int), n)
            }
        }
    };

    let mut res: Vec<char> = int_to_vec(total_area_val);
    res.push('\n');
    res
}
// </vc-code>


}

fn main() {}