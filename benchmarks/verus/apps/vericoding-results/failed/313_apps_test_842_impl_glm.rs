// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0
}

spec fn extract_first_line(s: Seq<char>) -> Seq<char>
    recommends s.len() > 0
{
    let newline_pos = find_first_newline(s);
    if newline_pos == -1 { s } else { s.subrange(0, newline_pos) }
}

spec fn find_first_newline(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        -1
    } else if s[0] == '\n' {
        0
    } else {
        let rest_result = find_first_newline(s.subrange(1, s.len() as int));
        if rest_result == -1 { -1 } else { rest_result + 1 }
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        Seq::empty() 
    } else { 
        reverse_string(s.subrange(1, s.len() as int)).push(s[0]) 
    }
}

spec fn valid_output(result: Seq<char>, input: Seq<char>) -> bool
    recommends input.len() > 0
{
    result.len() >= 1 &&
    result[result.len() - 1] == '\n' &&
    exists|n: Seq<char>| 
        n == extract_first_line(input) &&
        result == n.add(reverse_string(n)).push('\n')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed character literal for newline */
fn find_first_newline_exec(v: &Vec<char>) -> isize {
    for i in 0..v.len() {
        if v[i] == '\n' {
            return i as isize;
        }
    }
    -1
}

/* helper modified by LLM (iteration 4): replaced rev() with forward loop to avoid compilation error */
fn reverse_string_exec(s: &Vec<char>) -> Vec<char> {
    let mut reversed = Vec::new();
    let len = s.len();
    for i in 0..len {
        reversed.push(s[len - 1 - i]);
    }
    reversed
}

/* helper modified by LLM (iteration 3): updated to use isize return type from find_first_newline_exec */
fn extract_first_line_exec(v: &Vec<char>) -> Vec<char> {
    let newline_index = find_first_newline_exec(v);
    if newline_index == -1 {
        v.clone()
    } else {
        v[0..newline_index as usize].to_vec()
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_output(result@, stdin_input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed character literal for newline */
    let first_line = extract_first_line_exec(&stdin_input);
    let reversed_line = reverse_string_exec(&first_line);
    let mut result = first_line;
    result.extend(reversed_line);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}