// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_distinct(s: Seq<char>) -> int {
    s.to_set().len() as int
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    input[input.len() - 1] == '\n' &&
    input.len() >= 2 &&
    forall|i: int| 0 <= i < input.len() - 1 ==> 'a' <= input[i] && input[i] <= 'z'
}

spec fn correct_output(username: Seq<char>, output: Seq<char>) -> bool {
    let distinct_count = count_distinct(username);
    (distinct_count % 2 == 1 ==> output == seq!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n']) &&
    (distinct_count % 2 == 0 ==> output == seq!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n'])
}
// </vc-preamble>

// <vc-helpers>
spec fn distinct_char_count(s: Seq<char>) -> int {
    s.to_set().len() as int
}

/* helper modified by LLM (iteration 5): removed byte literal b'a' */
proof fn distinct_count_equivalence(s: Seq<char>)
    ensures count_distinct(s) == distinct_char_count(s)
{
}

fn count_unique_chars(chars: &Vec<char>, end: usize) -> (result: usize)
    requires
        end <= chars@.len(),
        forall|i: int| 0 <= i < end ==> 'a' <= chars@[i] && chars@[i] <= 'z'
    ensures
        result == count_distinct(chars@.subrange(0, end as int)) as usize
{
    let mut seen = [false; 26];
    let mut count = 0;
    let mut i = 0;
    
    while i < end
        invariant
            i <= end,
            count <= 26,
            count == chars@.subrange(0, i as int).to_set().len()
    {
        let ch = chars[i];
        let idx = (ch as u8 - 97u8) as usize;
        
        if !seen[idx] {
            seen[idx] = true;
            count += 1;
        }
        i += 1;
    }
    
    proof {
        distinct_count_equivalence(chars@.subrange(0, end as int));
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures ({
        let username = input@.subrange(0, input@.len() - 1);
        correct_output(username, output@)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): unchanged implementation */
    let username_len = input.len() - 1;
    let distinct_count = count_unique_chars(&input, username_len);
    
    if distinct_count % 2 == 1 {
        vec!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n']
    } else {
        vec!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n']
    }
}
// </vc-code>


}

fn main() {}