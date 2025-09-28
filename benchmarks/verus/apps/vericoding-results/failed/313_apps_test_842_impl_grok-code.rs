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
/* helper modified by LLM (iteration 5): removed invalid .as_int() from ensures for i32 type */
fn find_first_newline_exec(s: &Vec<char>) -> (result: i32)
    ensures
        find_first_newline(s@) == result,
{
    let slen = s.len() as i32;
    let mut i = 0;
    while i < slen
        invariant
            0 <= i <= slen,
            forall |j: int| 0 <= j < i ==> s@[j] != '\n'
        decreases slen - i,
    {
        if s[i as usize] == '\n' {
            return i;
        }
        i += 1;
    }
    return -1;
}

/* helper modified by LLM (iteration 5): fixed invariant to use .drop() for subsequence extraction */
fn reverse_string_exec(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == reverse_string(s@),
{
    let slen = s.len();
    let mut i = slen;
    let mut result = Vec::new();
    while i > 0
        invariant
            0 <= i <= slen,
            result@ == reverse_string(s@.drop(i as int))
        decreases i,
    {
        i -= 1;
        result.push(s[i]);
    }
    result
}

fn extract_first_line_exec(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == extract_first_line(s@),
{
    let pos: i32 = find_first_newline_exec(s);
    let slen = s.len();
    let end = if pos == -1 { slen } else { pos as usize };
    s[0..end].to_vec()
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_output(result@, stdin_input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented using helper functions */
{
    let n = extract_first_line_exec(&stdin_input);
    let rev = reverse_string_exec(&n);
    let mut result = n;
    result.append(&mut rev);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}