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
/* helper modified by LLM (iteration 5): fixed syntax errors by using tracked mut for seen, fixed indexing syntax to .index() */
fn count_distinct_exec(input: &Vec<char>, start: usize, end: usize) -> (result: usize)
    requires
        start <= end <= input.len(),
        forall|i: usize| start <= i < end ==> 'a' <= input[i] && input[i] <= 'z'
    ensures
        result as int == count_distinct(input@.subrange(start as int, end as int))
{
    let mut count = 0;
    tracked mut seen: Seq<bool> = seq![false; 26];
    tracked s: Seq<char> = input@.subrange(start as int, end as int);
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            count as int == count_distinct(s.subrange(0, i as int - start as int)),
            forall|j: int| 0 <= j < 26 ==> seen.index(j) == (exists|k: int| 0 <= k < i as int - start as int ==> s.index(k) == (('a' as u8 + j as u8) as char))
        decreases end - i
    {
        let c = input[i];
        let idx: int = (c as u8 - 'a' as u8) as int;
        let old_seen = seen.index(idx);
        if old_seen {
            // already seen
        } else {
            proof { seen = seen.update(idx, true); }
            count += 1;
        }
        i += 1;
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
/* code modified by LLM (iteration 5): updated to use .subrange for username specification to ensure correctness */
{
    let username_len = input.len() - 1;
    let distinct_count = count_distinct_exec(&input, 0, username_len);
    let output_seq: Vec<char> = if distinct_count % 2 == 1 {
        vec!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n']
    } else {
        vec!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n']
    };
    output_seq
}
// </vc-code>


}

fn main() {}