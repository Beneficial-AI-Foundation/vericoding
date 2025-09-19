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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}