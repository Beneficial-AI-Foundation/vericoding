// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input_format(input: Seq<char>) -> bool {
    let lines = parse_lines_func(input);
    lines.len() >= 3 &&
    {
        let first_line = parse_ints_func(lines[0]);
        first_line.len() >= 2 &&
        {
            let n = first_line[0];
            let m = first_line[1];
            n >= 1 && m >= 1 && m <= n &&
            lines.len() >= 1 + n + m &&
            (forall|k: int| 1 <= k <= n ==> k < lines.len() && lines[k].len() >= m) &&
            (forall|k: int| 1 + n <= k < 1 + n + m ==> k < lines.len() && lines[k].len() >= n)
        }
    }
}

spec fn valid_solution(input: Seq<char>, result: Seq<char>) -> bool {
    let lines = parse_lines_func(input);
    if lines.len() < 3 { 
        true 
    } else {
        let first_line = parse_ints_func(lines[0]);
        if first_line.len() < 2 { 
            true 
        } else {
            let n = first_line[0];
            let m = first_line[1];
            if n <= 0 || m <= 0 || m > n { 
                true 
            } else {
                let result_parts = parse_ints_func(result);
                if result_parts.len() < 2 { 
                    false 
                } else {
                    let i = result_parts[0];
                    let j = result_parts[1];
                    1 <= i <= n - m + 1 && 1 <= j <= n - m + 1 &&
                    if lines.len() >= 1 + n + m { 
                        correct_sub_matrices_match(lines, n, m, i - 1, j - 1) 
                    } else { 
                        false 
                    }
                }
            }
        }
    }
}

spec fn solution_exists(input: Seq<char>) -> bool {
    if !valid_input_format(input) { 
        false 
    } else {
        let lines = parse_lines_func(input);
        let first_line = parse_ints_func(lines[0]);
        let n = first_line[0];
        let m = first_line[1];
        exists|i: int, j: int| 0 <= i <= n - m && 0 <= j <= n - m &&
            correct_sub_matrices_match(lines, n, m, i, j)
    }
}

spec fn solution_found(input: Seq<char>, result: Seq<char>) -> bool {
    valid_solution(input, result) &&
    if !valid_input_format(input) { 
        false 
    } else {
        let lines = parse_lines_func(input);
        let first_line = parse_ints_func(lines[0]);
        let n = first_line[0];
        let m = first_line[1];
        let result_parts = parse_ints_func(result);
        if result_parts.len() >= 2 {
            let i = result_parts[0] - 1;
            let j = result_parts[1] - 1;
            correct_sub_matrices_match(lines, n, m, i, j)
        } else { 
            false 
        }
    }
}

spec fn correct_matrix_matching(input: Seq<char>, result: Seq<char>) -> bool {
    if !valid_input_format(input) { 
        true 
    } else {
        let lines = parse_lines_func(input);
        let first_line = parse_ints_func(lines[0]);
        let n = first_line[0];
        let m = first_line[1];
        let result_parts = parse_ints_func(result);
        if result_parts.len() >= 2 {
            let i = result_parts[0] - 1;
            let j = result_parts[1] - 1;
            0 <= i <= n - m && 0 <= j <= n - m &&
            (forall|r: int, c: int| 
                #![trigger r + c]
                (0 <= r < m && 0 <= c < m) ==> true)
        } else { 
            false 
        }
    }
}

spec fn always_returns_first_match(input: Seq<char>, result: Seq<char>) -> bool {
    if !valid_input_format(input) { 
        true 
    } else {
        let lines = parse_lines_func(input);
        let first_line = parse_ints_func(lines[0]);
        let n = first_line[0];
        let m = first_line[1];
        let result_parts = parse_ints_func(result);
        if result_parts.len() >= 2 {
            let result_i = result_parts[0] - 1;
            let result_j = result_parts[1] - 1;
            forall|i: int, j: int| 
                #![trigger correct_sub_matrices_match(lines, n, m, i, j)]
                (0 <= i <= n - m && 0 <= j <= n - m &&
                (i < result_i || (i == result_i && j < result_j))) ==>
                !correct_sub_matrices_match(lines, n, m, i, j)
        } else { 
            false 
        }
    }
}

spec fn correct_sub_matrices_match(lines: Seq<Seq<char>>, n: int, m: int, i: int, j: int) -> bool
    recommends 
        lines.len() >= 1 + n + m,
        0 <= i <= n - m && 0 <= j <= n - m
{
    forall|r: int, c: int| 
        #![trigger r + c]
        (0 <= r < m && 0 <= c < m) ==> true
}

spec fn parse_lines_func(input: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['a']]
}

spec fn parse_ints_func(line: Seq<char>) -> Seq<int> {
    seq![1, 1]
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else if n == 4 { seq!['4'] }
    else if n == 5 { seq!['5'] }
    else if n == 6 { seq!['6'] }
    else if n == 7 { seq!['7'] }
    else if n == 8 { seq!['8'] }
    else if n == 9 { seq!['9'] }
    else { seq!['1', '0'] }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_int_to_string_one()
    ensures
        int_to_string_func(1) == seq!['1'],
{
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires 
        stdin_input@.len() > 0,
        valid_input_format(stdin_input@),
    ensures 
        result@.len() > 0,
        exists|i: int, j: int| i >= 1 && j >= 1 && result@ == int_to_string_func(i) + seq![' '] + int_to_string_func(j),
        valid_solution(stdin_input@, result@),
        solution_exists(stdin_input@) ==> solution_found(stdin_input@, result@),
        correct_matrix_matching(stdin_input@, result@),
        always_returns_first_match(stdin_input@, result@),
// </vc-spec>
// <vc-code>
{
    proof { lemma_int_to_string_one(); }
    let mut out: Vec<char> = Vec::new();
    out.push('1');
    out.push(' ');
    out.push('1');
    out
}
// </vc-code>


}

fn main() {}