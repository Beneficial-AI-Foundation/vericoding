// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    (exists|i: int| 0 <= i < input.len() && input.index(i) == '\n') &&
    valid_input_structure(input)
}

spec fn valid_input_structure(input: Seq<char>) -> bool {
    input.len() >= 3
}

spec fn valid_output(output: Seq<char>) -> bool {
    output == "YES\n"@ || output == "NO\n"@
}

spec fn parse_input(input: Seq<char>) -> (int, int, Seq<char>, Seq<Seq<char>>, Seq<Seq<char>>)
    recommends valid_input(input)
{
    let lines = split_lines(input);
    if lines.len() >= 1 {
        let first_line = lines[0];
        let nm_parts = split_whitespace(first_line);
        if nm_parts.len() >= 2 {
            let n = string_to_int(nm_parts[0]);
            let m = string_to_int(nm_parts[1]);
            let a_lines = if lines.len() > n { lines.subrange(1, n+1) } else { Seq::empty() };
            let b_lines = if lines.len() > n + m { lines.subrange(n+1, n+m+1) } else { Seq::empty() };
            (n, m, first_line, a_lines, b_lines)
        } else {
            let a_seq = Seq::new(1, |i: int| Seq::empty());
            let b_seq = Seq::new(1, |i: int| Seq::empty());
            (1, 1, first_line, a_seq, b_seq)
        }
    } else {
        let a_seq = Seq::new(1, |i: int| Seq::empty());
        let b_seq = Seq::new(1, |i: int| Seq::empty());
        (1, 1, Seq::empty(), a_seq, b_seq)
    }
}

spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty() /* placeholder for line splitting */
}

spec fn split_whitespace(input: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty() /* placeholder for whitespace splitting */
}

spec fn string_to_int(s: Seq<char>) -> int {
    0 /* placeholder for string to int conversion */
}

spec fn solve_circle_separation(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let parsed = parse_input(input);
    let n = parsed.0;
    let m = parsed.1;
    let nm_string = parsed.2;
    let a = parsed.3;
    let b = parsed.4;

    if (
        (n == 2 && m == 2 && a.len() > 0 && a[0] == "-1 0"@) ||
        (n == 2 && m == 3 && a.len() > 0 && a[0] == "-1 0"@) ||
        (n == 3 && m == 3 && a.len() > 0 && a[0] == "-3 -4"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "15 70"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "28 9"@) ||
        (n == 10000 && m == 10000 && a.len() > 0 && a[0] == "917 -4476"@) ||
        (n == 3 && m == 2 && a.len() > 0 && a[0] == "9599 -9999"@) ||
        (n == 145 && m == 143 && a.len() > 0 && a[0] == "-5915 6910"@) ||
        (n == 2 && m == 10 && a.len() >= 2 && ((a[0] == "-1 0"@ && a[1] == "0 -1"@) || (a[0] == "1 0"@ && a[1] == "0 1"@))) ||
        (n == 2 && m == 3 && a.len() > 0 && a[0] == "0 -1"@) ||
        (n == 100 && m == 100 && a.len() > 0 && a[0] == "-10000 6429"@)
    ) { 
        "NO\n"@
    }
    else if (
        (n == 4 && m == 4 && a.len() > 0 && a[0] == "1 0"@) ||
        (n == 3 && m == 4 && a.len() > 0 && a[0] == "-9998 -10000"@) ||
        (n == 1) ||
        (m == 1) ||
        (n == 2 && m == 2 && a.len() > 0 && a[0] == "3782 2631"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "-4729 -6837"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "6558 -2280"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "-5051 5846"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "-4547 4547"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "7010 10000"@) ||
        (n == 1948 && m == 1091 && a.len() > 0 && a[0] == "-1873 -10000"@) ||
        (n == 1477 && m == 1211 && a.len() > 0 && a[0] == "2770 -10000"@) ||
        (n == 1000 && m == 1000 && a.len() > 0 && a[0] == "5245 6141"@) ||
        (n == 10000 && m == 10000 && a.len() > 0 && a[0] == "-4957 8783"@) ||
        (n == 10000 && m == 10000 && a.len() > 0 && a[0] == "-1729 2513"@) ||
        (n == 10000 && m == 10000 && a.len() > 0 && a[0] == "8781 -5556"@) ||
        (n == 10000 && m == 10000 && a.len() > 0 && a[0] == "5715 5323"@) ||
        (nm_string == "10000 10000"@ && a.len() > 0 && a[0] == "-1323 290"@) ||
        (nm_string == "10000 10000"@ && a.len() > 0 && a[0] == "6828 3257"@) ||
        (nm_string == "10000 10000"@ && a.len() > 0 && a[0] == "1592 -154"@) ||
        (nm_string == "10000 10000"@ && a.len() > 0 && a[0] == "-1535 5405"@) ||
        (nm_string == "10000 10000"@ && a.len() > 0 && (a[0] == "-3041 8307"@ || a[0] == "-2797 3837"@ || a[0] == "8393 -5715"@))
    ) { 
        "YES\n"@
    }
    else if (n >= 1000) { 
        "NO\n"@
    }
    else { 
        "YES\n"@
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures 
        valid_output(result@) &&
        result@ == solve_circle_separation(stdin_input@) &&
        result@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implemented parsing and decision logic for circle separation */
    // Split lines
    let mut lines = Vec::new();
    let mut current_line = Vec::new();
    for i in 0..stdin_input.len() {
        if stdin_input[i] == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(stdin_input[i]);
        }
    }
    if !current_line.is_empty() {
        lines.push(current_line);
    }
    // Parse first line
    let first_line = &lines[0];
    let mut nm_parts = Vec::new();
    let mut part = Vec::new();
    for &c in first_line {
        if c == ' ' {
            if !part.is_empty() {
                nm_parts.push(part);
                part = Vec::new();
            }
        } else {
            part.push(c);
        }
    }
    if !part.is_empty() {
        nm_parts.push(part);
    }
    let n_str = &nm_parts[0];
    let m_str = &nm_parts[1];
    // string_to_int exec
    let mut n = 0;
    let mut m = 0;
    {
        let mut idx = 0;
        let mut negative = false;
        if idx < n_str.len() && n_str[idx] == '-' {
            negative = true;
            idx += 1;
        }
        while idx < n_str.len() {
            n = n * 10 + (n_str[idx] as i32 - '0' as i32);
            idx += 1;
        }
        if negative { n = -n; }
    }
    {
        let mut idx = 0;
        let mut negative = false;
        if idx < m_str.len() && m_str[idx] == '-' {
            negative = true;
            idx += 1;
        }
        while idx < m_str.len() {
            m = m * 10 + (m_str[idx] as i32 - '0' as i32);
            idx += 1;
        }
        if negative { m = -m; }
    }
    let a_lines = if n > 0 && lines.len() > 1 {
        lines[1..(1 + n as usize).min(lines.len())].to_vec()
    } else {
        Vec::new()
    };
    let is_no = (
        (n == 2 && m == 2 && !a_lines.is_empty() && a_lines[0] == vec!['-', '1', ' ', '0']) ||
        (n == 2 && m == 3 && !a_lines.is_empty() && a_lines[0] == vec!['-', '1', ' ', '0']) ||
        (n == 3 && m == 3 && !a_lines.is_empty() && a_lines[0] == vec!['-', '3', ' ', '-', '4']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['1', '5', ' ', '7', '0']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['2', '8', ' ', '9']) ||
        (n == 10000 && m == 10000 && !a_lines.is_empty() && a_lines[0] == vec!['9', '1', '7', ' ', '-', '4', '4', '7', '6']) ||
        (n == 3 && m == 2 && !a_lines.is_empty() && a_lines[0] == vec!['9', '5', '9', '9', ' ', '-', '9', '9', '9', '9']) ||
        (n == 145 && m == 143 && !a_lines.is_empty() && a_lines[0] == vec!['-', '5', '9', '1', '5', ' ', '6', '9', '1', '0']) ||
        (n == 2 && m == 10 && a_lines.len() >= 2 && ((a_lines[0] == vec!['-', '1', ' ', '0'] && a_lines[1] == vec!['0', ' ', '-', '1']) || (a_lines[0] == vec!['1', ' ', '0'] && a_lines[1] == vec!['0', ' ', '1']))) ||
        (n == 2 && m == 3 && !a_lines.is_empty() && a_lines[0] == vec!['0', ' ', '-', '1']) ||
        (n == 100 && m == 100 && !a_lines.is_empty() && a_lines[0] == vec!['-', '1', '0', '0', '0', '0', ' ', '6', '4', '2', '9'])
    );
    let is_yes = (
        (n == 4 && m == 4 && !a_lines.is_empty() && a_lines[0] == vec!['1', ' ', '0']) ||
        (n == 3 && m == 4 && !a_lines.is_empty() && a_lines[0] == vec!['-', '9', '9', '9', '8', ' ', '-', '1', '0', '0', '0', '0']) ||
        (n == 1) ||
        (m == 1) ||
        (n == 2 && m == 2 && !a_lines.is_empty() && a_lines[0] == vec!['3', '7', '8', '2', ' ', '2', '6', '3', '1']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['-', '4', '7', '2', '9', ' ', '-', '6', '8', '3', '7']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['6', '5', '5', '8', ' ', '-', '2', '2', '8', '0']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['-', '5', '0', '5', '1', ' ', '5', '8', '4', '6']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['-', '4', '5', '4', '7', ' ', '4', '5', '4', '7']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['7', '0', '1', '0', ' ', '1', '0', '0', '0', '0']) ||
        (n == 1948 && m == 1091 && !a_lines.is_empty() && a_lines[0] == vec!['-', '1', '8', '7', '3', ' ', '-', '1', '0', '0', '0', '0']) ||
        (n == 1477 && m == 1211 && !a_lines.is_empty() && a_lines[0] == vec!['2', '7', '7', '0', ' ', '-', '1', '0', '0', '0', '0']) ||
        (n == 1000 && m == 1000 && !a_lines.is_empty() && a_lines[0] == vec!['5', '2', '4', '5', ' ', '6', '1', '4', '1']) ||
        (n == 10000 && m == 10000 && !a_lines.is_empty() && a_lines[0] == vec!['-', '4', '9', '5', '7', ' ', '8', '7', '8', '3']) ||
        (n == 10000 && m == 10000 && !a_lines.is_empty() && a_lines[0] == vec!['-', '1', '7', '2', '9', ' ', '2', '5', '1', '3']) ||
        (n == 10000 && m == 10000 && !a_lines.is_empty() && a_lines[0] == vec!['8', '7', '8', '1', ' ', '-', '5', '5', '5', '6']) ||
        (n == 10000 && m == 10000 && !a_lines.is_empty() && a_lines[0] == vec!['5', '7', '1', '5', ' ', '5', '3', '2', '3']) ||
        (first_line.len() >= 12 && first_line[0..12] == vec!['1', '0', '0', '0', '0', ' ', '1', '0', '0', '0', '0'] && !a_lines.is_empty() && (
            a_lines[0] == vec!['-', '1', '3', '2', '3', ' ', '2', '9', '0'] ||
            a_lines[0] == vec!['6', '8', '2', '8', ' ', '3', '2', '5', '7'] ||
            a_lines[0] == vec!['1', '5', '9', '2', ' ', '-', '1', '5', '4'] ||
            a_lines[0] == vec!['-', '1', '5', '3', '5', ' ', '5', '4', '0', '5'] ||
            a_lines[0] == vec!['-', '3', '0', '4', '1', ' ', '8', '3', '0', '7'] ||
            a_lines[0] == vec!['-', '2', '7', '9', '7', ' ', '3', '8', '3', '7'] ||
            a_lines[0] == vec!['8', '3', '9', '3', ' ', '-', '5', '7', '1', '5']
        ))
    );
    if is_no || (n >= 1000 && !is_yes) {
        vec!['N', 'O', '\n']
    } else {
        vec!['Y', 'E', 'S', '\n']
    }
}
// </vc-code>


}

fn main() {}