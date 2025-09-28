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
/* helper modified by LLM (iteration 3): changed `lemma fn` to `proof fn` and added cast to int */
#[verifier::spinoff_prover]
proof fn lemma_find_first_newline_is_i(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        s[i] == '\n',
        forall|j: int| 0 <= j < i ==> s[j] != '\n',
    ensures find_first_newline(s) == i,
    decreases i,
{
    if i > 0 {
        lemma_find_first_newline_is_i(s.subrange(1, s.len() as int), i - 1);
    }
}

/* helper modified by LLM (iteration 3): changed `lemma fn` to `proof fn` and added cast to int */
#[verifier::spinoff_prover]
proof fn lemma_find_first_newline_is_minus_one(s: Seq<char>)
    requires forall|j: int| 0 <= j < s.len() ==> s[j] != '\n',
    ensures find_first_newline(s) == -1,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_find_first_newline_is_minus_one(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 4): fixed compilation error (type mismatch) by adding casts to i64 */
fn find_first_newline_exec(s: &Vec<char>) -> (result: i64)
    ensures result == find_first_newline(s@),
{
    let mut i: i64 = 0;
    while i < s.len() as i64
        invariant
            0 <= i <= s.len() as i64,
            forall|j: int| 0 <= j < i ==> s@[j] != '\n',
        decreases (s.len() as i64) - i,
    {
        if s[i as usize] == '\n' {
            proof { lemma_find_first_newline_is_i(s@, i as int); }
            return i;
        }
        i = i + 1;
    }
    proof { lemma_find_first_newline_is_minus_one(s@); }
    return -1;
}

fn extract_first_line_exec(s: &Vec<char>) -> (line: Vec<char>)
    requires s.len() > 0,
    ensures line@ == extract_first_line(s@),
{
    let newline_pos = find_first_newline_exec(s);
    if newline_pos == -1 {
        s.clone()
    } else {
        let mut line = s.clone();
        line.truncate(newline_pos as usize);
        line
    }
}

fn reverse_string_exec(s: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == reverse_string(s@),
{
    let mut result = Vec::new();
    let mut i = s.len();
    while i > 0
        invariant
            0 <= i <= s.len(),
            result@ == reverse_string(s@.subrange(i as int, s.len() as int)),
        decreases i,
    {
        i = i - 1;
        result.push(s[i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_output(result@, stdin_input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): updated comment, logic unchanged as error was in helpers */
    let first_line = extract_first_line_exec(&stdin_input);
    let mut reversed_line = reverse_string_exec(&first_line);
    
    let mut result = first_line;
    result.append(&mut reversed_line);
    result.push('\n');

    proof {
        let n = extract_first_line(stdin_input@);
        assert(result@ == n.add(reverse_string(n)).push('\n'));
        assert(valid_output(result@, stdin_input@));
    }
    
    result
}
// </vc-code>


}

fn main() {}