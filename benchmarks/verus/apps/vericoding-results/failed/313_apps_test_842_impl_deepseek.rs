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

proof fn lemma_find_first_newline_nonnegative(s: Seq<char>) 
    ensures 
        find_first_newline(s) >= -1,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_find_first_newline_nonnegative(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_extract_first_line_properties(s: Seq<char>) 
    requires 
        s.len() > 0,
    ensures 
        extract_first_line(s).len() > 0,
    decreases s.len()
{
    let newline_pos = find_first_newline(s);
    if newline_pos == -1 {
    } else {
        assert(newline_pos >= 0);
    }
}

proof fn lemma_reverse_string_length(s: Seq<char>) 
    ensures 
        reverse_string(s).len() == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_reverse_string_length(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 5): Fix subrange method usage with proper types */
fn extract_first_line_exec(s: &Vec<char>) -> (result: Vec<char>)
    requires
        s@.len() > 0,
    ensures
        result@ == extract_first_line(s@)
{
    let mut i: usize = 0;
    let ghost s_seq = s@;
    
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j && j < i ==> s_seq[j] != '\n',
        decreases s.len() - i
    {
        if s[i] == '\n' {
            break;
        }
        i = i + 1;
    }
    
    let mut result = Vec::new();
    let mut j: usize = 0;
    
    while j < i
        invariant
            j <= i,
            result@ == s_seq.subrange(0, j as int),
        decreases i - j
    {
        result.push(s[j]);
        j = j + 1;
    }
    
    result
}

/* helper modified by LLM (iteration 5): Fix reverse string implementation with proper indexing */
fn reverse_string_exec(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == reverse_string(s@)
{
    let mut result = Vec::new();
    let mut i: usize = s.len();
    let ghost s_seq = s@;
    
    while i > 0
        invariant
            i <= s.len(),
            result@ == reverse_string(s_seq.subrange(i as int, s.len() as int)),
        decreases i
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
    /* code modified by LLM (iteration 5): Fix type conversions and use proper sequence operations */
    let stdin_seq = stdin_input@;
    
    proof {
        lemma_find_first_newline_nonnegative(stdin_seq);
        lemma_extract_first_line_properties(stdin_seq);
    }
    
    let first_line = extract_first_line_exec(&stdin_input);
    let reversed = reverse_string_exec(&first_line);
    
    let mut result = first_line;
    let ghost result_seq = result@;
    
    let mut i: usize = 0;
    while i < reversed.len()
        invariant
            i <= reversed.len(),
            result@ == result_seq.add(reversed@.subrange(0, i as int)),
        decreases reversed.len() - i
    {
        result.push(reversed[i]);
        i = i + 1;
    }
    
    result.push('\n');
    
    proof {
        lemma_reverse_string_length(extract_first_line(stdin_seq));
    }
    
    result
}
// </vc-code>


}

fn main() {}