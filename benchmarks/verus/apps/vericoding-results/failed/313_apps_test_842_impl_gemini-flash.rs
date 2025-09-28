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
/* helper modified by LLM (iteration 5): Added `requires` clause to `lemma_find_first_newline_non_negative_if_exists` */
proof fn lemma_find_first_newline_non_negative_if_exists(s: Seq<char>)
    requires s.len() >= 0
    ensures (find_first_newline(s) >= -1)
    decreases s.len()
{
    if s.len() == 0 {
        // find_first_newline returns -1, which satisfies the ensurs clause
    } else if s[0] == '
' {
        // find_first_newline returns 0, which satisfies the ensurs clause
    } else {
        let rest_result = find_first_newline(s.subrange(1, s.len() as int));
        lemma_find_first_newline_non_negative_if_exists(s.subrange(1, s.len() as int));
        // The recursive call satisfies the ensures clause,
        // and if rest_result != -1, then rest_result + 1 >= 0.
        assert(rest_result >= -1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_output(result@, stdin_input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type mismatches with `int` and `usize` where necessary */
{
    let s_seq = stdin_input@;
    let first_line_seq = extract_first_line(s_seq);

    let mut extracted_chars: Vec<char> = Vec::new();

    lemma_find_first_newline_non_negative_if_exists(s_seq);
    let newline_pos: int = find_first_newline(s_seq);

    if newline_pos == -1 {
        extracted_chars = stdin_input;
    } else {
        let mut i: usize = 0;
        assert(newline_pos >= 0);
        while (i as int) < newline_pos
            invariant
                s_seq == stdin_input@,
                extracted_chars@ == s_seq.subrange(0, i as int),
                (i as int) <= newline_pos,
                newline_pos == find_first_newline(s_seq),
                newline_pos >= 0
            decreases (newline_pos - i as int)
        {
            extracted_chars.push(stdin_input[i as usize]);
            i = i + 1;
        }
    }

    assert(extracted_chars@ == first_line_seq);

    let mut reversed_extracted_chars: Vec<char> = Vec::new();
    let mut j: usize = extracted_chars.len();

    while j > 0
        invariant
            extracted_chars@ == first_line_seq,
            reversed_extracted_chars@ == reverse_string(extracted_chars@.subrange(j as int, extracted_chars.len() as int)),
            j <= extracted_chars.len()
        decreases j
    {
        reversed_extracted_chars.push(extracted_chars[(j - 1) as usize]);
        j = j - 1;
    }
    
    assert(reversed_extracted_chars@ == reverse_string(first_line_seq));

    let mut result: Vec<char> = Vec::new();
    let mut k: usize = 0;
    while k < extracted_chars.len()
        invariant
            extracted_chars@ == first_line_seq,
            result@ == first_line_seq.subrange(0, k as int),
            k <= extracted_chars.len()
        decreases (extracted_chars.len() - k)
    {
        result.push(extracted_chars[k as usize]);
        k = k + 1;
    }

    let mut l: usize = 0;
    while l < reversed_extracted_chars.len()
        invariant(
            reversed_extracted_chars@ == reverse_string(first_line_seq),
            result@ == first_line_seq.add(reverse_string(first_line_seq).subrange(0, l as int)),
            l <= reversed_extracted_chars.len()
        )
        decreases (reversed_extracted_chars.len() - l)
    {
        result.push(reversed_extracted_chars[l as usize]);
        l = l + 1;
    }

    result.push('
');

    result
}
// </vc-code>


}

fn main() {}