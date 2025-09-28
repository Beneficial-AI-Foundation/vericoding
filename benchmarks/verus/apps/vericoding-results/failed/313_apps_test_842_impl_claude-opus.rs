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
/* helper modified by LLM (iteration 5): Added lemmas to connect implementation to spec functions */

proof fn lemma_first_line_matches_extract(input: Seq<char>, first_line: Seq<char>, i: int)
    requires
        0 <= i <= input.len(),
        first_line.len() == i,
        forall|j: int| 0 <= j < i ==> first_line[j] == input[j],
        forall|j: int| 0 <= j < i ==> input[j] != '\n',
        i == input.len() || input[i] == '\n',
    ensures
        first_line == extract_first_line(input),
    decreases i
{
    if i == 0 {
        assert(first_line.len() == 0);
        if input.len() == 0 {
            assert(extract_first_line(input) == input);
            assert(first_line == Seq::<char>::empty());
        } else if input[0] == '\n' {
            assert(find_first_newline(input) == 0);
            assert(extract_first_line(input) == input.subrange(0, 0));
            assert(first_line == input.subrange(0, 0));
        }
    } else if i == input.len() {
        assert(forall|j: int| 0 <= j < input.len() ==> input[j] != '\n');
        lemma_no_newline_means_whole_string(input);
        assert(find_first_newline(input) == -1);
        assert(extract_first_line(input) == input);
        assert(first_line == input);
    } else {
        assert(input[i] == '\n');
        lemma_find_newline_at_position(input, i);
        assert(find_first_newline(input) == i);
        assert(extract_first_line(input) == input.subrange(0, i));
        assert(first_line == input.subrange(0, i));
    }
}

proof fn lemma_no_newline_means_whole_string(s: Seq<char>)
    requires
        forall|j: int| 0 <= j < s.len() ==> s[j] != '\n',
    ensures
        find_first_newline(s) == -1,
    decreases s.len()
{
    if s.len() == 0 {
        assert(find_first_newline(s) == -1);
    } else {
        assert(s[0] != '\n');
        let rest = s.subrange(1, s.len() as int);
        assert(forall|j: int| 0 <= j < rest.len() ==> rest[j] == s[j + 1]);
        assert(forall|j: int| 0 <= j < rest.len() ==> rest[j] != '\n');
        lemma_no_newline_means_whole_string(rest);
        assert(find_first_newline(rest) == -1);
        assert(find_first_newline(s) == -1);
    }
}

proof fn lemma_find_newline_at_position(s: Seq<char>, pos: int)
    requires
        0 <= pos < s.len(),
        s[pos] == '\n',
        forall|j: int| 0 <= j < pos ==> s[j] != '\n',
    ensures
        find_first_newline(s) == pos,
    decreases pos
{
    if pos == 0 {
        assert(s[0] == '\n');
        assert(find_first_newline(s) == 0);
    } else {
        assert(s[0] != '\n');
        let rest = s.subrange(1, s.len() as int);
        assert(rest[pos - 1] == s[pos]);
        assert(rest[pos - 1] == '\n');
        assert(forall|j: int| 0 <= j < pos - 1 ==> rest[j] == s[j + 1]);
        assert(forall|j: int| 0 <= j < pos - 1 ==> rest[j] != '\n');
        lemma_find_newline_at_position(rest, pos - 1);
        assert(find_first_newline(rest) == pos - 1);
        assert(find_first_newline(s) == pos);
    }
}

proof fn lemma_reverse_implementation(first_line: Seq<char>, result_part: Seq<char>, k: int)
    requires
        0 <= k <= first_line.len(),
        result_part.len() == k,
        forall|m: int| 0 <= m < k ==> result_part[m] == first_line[first_line.len() - 1 - m],
    ensures
        result_part == reverse_string(first_line.subrange(first_line.len() - k, first_line.len() as int)),
    decreases k
{
    if k == 0 {
        assert(result_part == Seq::<char>::empty());
        assert(first_line.subrange(first_line.len() - 0, first_line.len() as int) == Seq::<char>::empty());
        assert(reverse_string(Seq::<char>::empty()) == Seq::<char>::empty());
    } else {
        let sub = first_line.subrange(first_line.len() - k, first_line.len() as int);
        assert(sub.len() == k);
        assert(sub[0] == first_line[first_line.len() - k]);
        let sub_rest = sub.subrange(1, sub.len() as int);
        assert(sub_rest == first_line.subrange(first_line.len() - k + 1, first_line.len() as int));
        
        let result_prefix = result_part.subrange(0, (k - 1) as int);
        assert(forall|m: int| 0 <= m < k - 1 ==> result_prefix[m] == first_line[first_line.len() - 1 - m]);
        
        lemma_reverse_implementation(first_line, result_prefix, k - 1);
        assert(result_prefix == reverse_string(sub_rest));
        assert(result_part[k - 1] == first_line[first_line.len() - k]);
        assert(result_part[k - 1] == sub[0]);
        assert(result_part == reverse_string(sub_rest).push(sub[0]));
        assert(result_part == reverse_string(sub));
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
    /* code modified by LLM (iteration 5): Fixed type annotations for empty sequences */
    let mut first_line = Vec::new();
    let mut i: usize = 0;
    
    while i < stdin_input.len()
        invariant
            0 <= i <= stdin_input.len(),
            first_line@.len() == i,
            forall|j: int| 0 <= j < i ==> first_line@[j] == stdin_input@[j],
            forall|j: int| 0 <= j < i ==> stdin_input@[j] != '\n',
        decreases stdin_input.len() - i
    {
        if stdin_input[i] == '\n' {
            break;
        }
        first_line.push(stdin_input[i]);
        i += 1;
    }
    
    proof {
        lemma_first_line_matches_extract(stdin_input@, first_line@, i as int);
        assert(first_line@ == extract_first_line(stdin_input@));
    }
    
    let mut result = Vec::new();
    let mut j: usize = 0;
    
    while j < first_line.len()
        invariant
            0 <= j <= first_line.len(),
            result@.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] == first_line@[k],
        decreases first_line.len() - j
    {
        result.push(first_line[j]);
        j += 1;
    }
    
    assert(result@ == first_line@);
    
    let mut k: usize = 0;
    let result_len_before_reverse = result.len();
    
    while k < first_line.len()
        invariant
            0 <= k <= first_line.len(),
            result_len_before_reverse == first_line.len(),
            result@.len() == first_line@.len() + k,
            forall|m: int| 0 <= m < first_line@.len() ==> result@[m] == first_line@[m],
            forall|m: int| 0 <= m < k ==> result@[first_line@.len() + m] == first_line@[first_line@.len() - 1 - m],
        decreases first_line.len() - k
    {
        result.push(first_line[first_line.len() - 1 - k]);
        k += 1;
    }
    
    proof {
        let reversed_part = result@.subrange(first_line@.len() as int, result@.len() as int);
        assert(reversed_part.len() == first_line@.len());
        assert(forall|m: int| 0 <= m < first_line@.len() ==> reversed_part[m] == first_line@[first_line@.len() - 1 - m]);
        lemma_reverse_implementation(first_line@, reversed_part, first_line@.len() as int);
        assert(reversed_part == reverse_string(first_line@));
        assert(result@ == first_line@.add(reversed_part));
        assert(result@ == first_line@.add(reverse_string(first_line@)));
    }
    
    result.push('\n');
    
    proof {
        assert(result@.len() >= 1);
        assert(result@[result@.len() - 1] == '\n');
        let n = first_line@;
        assert(n == extract_first_line(stdin_input@));
        assert(result@ == n.add(reverse_string(n)).push('\n'));
        assert(valid_output(result@, stdin_input@));
    }
    
    result
}
// </vc-code>


}

fn main() {}