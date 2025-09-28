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
/* helper modified by LLM (iteration 5): fixed type casting issues by using usize for actual length operations */
exec fn lemma_find_first_newline_correct(s: Seq<char>, pos: int)
    requires
        0 <= pos < s.len(),
        s[pos] == '\n',
        forall|i: int| 0 <= i < pos ==> s[i] != '\n',
    ensures find_first_newline(s) == pos
    decreases s.len()
{
    if pos == 0int {
        assert(s[0] == '\n');
    } else {
        let rest = s.subrange(1int, s.len());
        lemma_find_first_newline_correct(rest, pos - 1int);
        assert(find_first_newline(rest) == pos - 1int);
    }
}

exec fn lemma_reverse_string_len(s: Seq<char>)
    ensures reverse_string(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0nat {
    } else {
        lemma_reverse_string_len(s.subrange(1int, s.len()));
    }
}

exec fn lemma_extract_first_line_properties(s: Seq<char>)
    requires s.len() > 0
    ensures
        extract_first_line(s).len() <= s.len(),
        extract_first_line(s).len() > 0,
    decreases s.len()
{
    let newline_pos = find_first_newline(s);
    if newline_pos == -1int {
        assert(extract_first_line(s) == s);
    } else {
        assert(extract_first_line(s) == s.subrange(0, newline_pos));
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
    /* code modified by LLM (iteration 5): fixed type casting by using usize for length operations instead of int casting */
    let mut result = Vec::new();
    let mut first_line = Vec::new();
    let mut i = 0;
    
    while i < stdin_input.len()
        invariant
            0 <= i <= stdin_input.len(),
            first_line.len() == i,
            first_line@ == stdin_input@.subrange(0, i as int),
        decreases stdin_input.len() - i
    {
        if stdin_input[i] == '\n' {
            break;
        }
        first_line.push(stdin_input[i]);
        i = i + 1;
    }
    
    proof {
        lemma_extract_first_line_properties(stdin_input@);
    }
    
    for j in 0..first_line.len()
        invariant
            0 <= j <= first_line.len(),
            result.len() == j,
            result@ == first_line@.subrange(0, j as int),
    {
        result.push(first_line[j]);
    }
    
    let mut k = 0;
    while k < first_line.len()
        invariant
            0 <= k <= first_line.len(),
            result.len() == first_line.len() + k,
            result@.subrange(0, first_line.len() as int) == first_line@,
            result@.subrange(first_line.len() as int, result.len() as int) == 
                reverse_string(first_line@.subrange(0, k as int)),
        decreases first_line.len() - k
    {
        let idx = first_line.len() - 1 - k;
        result.push(first_line[idx]);
        
        proof {
            lemma_reverse_string_len(first_line@.subrange(0, (k + 1) as int));
        }
        
        k = k + 1;
    }
    
    result.push('\n');
    
    proof {
        lemma_reverse_string_len(first_line@);
        assert(result@.len() >= 1);
        assert(result@[result@.len() - 1] == '\n');
        
        let n = extract_first_line(stdin_input@);
        assert(n == first_line@);
        assert(result@ == n.add(reverse_string(n)).push('\n'));
    }
    
    result
}
// </vc-code>


}

fn main() {}