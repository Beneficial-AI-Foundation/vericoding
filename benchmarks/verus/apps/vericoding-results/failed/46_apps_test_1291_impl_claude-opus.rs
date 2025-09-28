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
/* helper modified by LLM (iteration 5): Added sequence comparison helper */
spec fn seq_equal(s1: Seq<char>, s2: Seq<char>) -> bool {
    s1.len() == s2.len() &&
    forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
}

fn vec_equals_str(v: &Vec<char>, s: &str) -> (result: bool)
    ensures result == seq_equal(v@, s@)
{
    if v.len() != s.len() {
        return false;
    }
    
    let s_chars: Vec<char> = s.chars().collect();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v.len() == s_chars.len(),
            forall|j: int| 0 <= j < i ==> v[j as int] == s_chars[j as int]
    {
        if v[i] != s_chars[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
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
    /* code modified by LLM (iteration 5): Fixed sequence comparison using helper function */
    let mut result = Vec::new();
    
    // Parse the first line to get n and m
    let mut i: usize = 0;
    let mut n: u32 = 0;
    let mut m: u32 = 0;
    let mut found_space = false;
    
    // Read n
    while i < stdin_input.len() {
        if stdin_input[i] == ' ' {
            found_space = true;
            i = i + 1;
            break;
        } else if stdin_input[i] >= '0' && stdin_input[i] <= '9' {
            n = n * 10 + ((stdin_input[i] as u32) - ('0' as u32));
        }
        i = i + 1;
    }
    
    // Read m
    while i < stdin_input.len() {
        if stdin_input[i] == '\n' {
            break;
        } else if stdin_input[i] >= '0' && stdin_input[i] <= '9' {
            m = m * 10 + ((stdin_input[i] as u32) - ('0' as u32));
        }
        i = i + 1;
    }
    
    // Move past the newline
    if i < stdin_input.len() && stdin_input[i] == '\n' {
        i = i + 1;
    }
    
    // Read the first line of A coordinates if it exists
    let mut first_a_line = Vec::new();
    if i < stdin_input.len() && n > 0 {
        while i < stdin_input.len() && stdin_input[i] != '\n' {
            first_a_line.push(stdin_input[i]);
            i = i + 1;
        }
    }
    
    // Check special cases based on n, m, and first A line
    let is_no_case = 
        (n == 2 && m == 2 && vec_equals_str(&first_a_line, "-1 0")) ||
        (n == 2 && m == 3 && vec_equals_str(&first_a_line, "-1 0")) ||
        (n == 3 && m == 3 && vec_equals_str(&first_a_line, "-3 -4")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "15 70")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "28 9")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "917 -4476")) ||
        (n == 3 && m == 2 && vec_equals_str(&first_a_line, "9599 -9999")) ||
        (n == 145 && m == 143 && vec_equals_str(&first_a_line, "-5915 6910")) ||
        (n == 2 && m == 3 && vec_equals_str(&first_a_line, "0 -1")) ||
        (n == 100 && m == 100 && vec_equals_str(&first_a_line, "-10000 6429"));
    
    let is_yes_case = 
        (n == 4 && m == 4 && vec_equals_str(&first_a_line, "1 0")) ||
        (n == 3 && m == 4 && vec_equals_str(&first_a_line, "-9998 -10000")) ||
        (n == 1) ||
        (m == 1) ||
        (n == 2 && m == 2 && vec_equals_str(&first_a_line, "3782 2631")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "-4729 -6837")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "6558 -2280")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "-5051 5846")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "-4547 4547")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "7010 10000")) ||
        (n == 1948 && m == 1091 && vec_equals_str(&first_a_line, "-1873 -10000")) ||
        (n == 1477 && m == 1211 && vec_equals_str(&first_a_line, "2770 -10000")) ||
        (n == 1000 && m == 1000 && vec_equals_str(&first_a_line, "5245 6141")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "-4957 8783")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "-1729 2513")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "8781 -5556")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "5715 5323")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "-1323 290")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "6828 3257")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "1592 -154")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "-1535 5405")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "-3041 8307")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "-2797 3837")) ||
        (n == 10000 && m == 10000 && vec_equals_str(&first_a_line, "8393 -5715"));
    
    if is_no_case {
        result.push('N');
        result.push('O');
        result.push('\n');
    } else if is_yes_case {
        result.push('Y');
        result.push('E');
        result.push('S');
        result.push('\n');
    } else if n >= 1000 {
        result.push('N');
        result.push('O');
        result.push('\n');
    } else {
        result.push('Y');
        result.push('E');
        result.push('S');
        result.push('\n');
    }
    
    result
}
// </vc-code>


}

fn main() {}