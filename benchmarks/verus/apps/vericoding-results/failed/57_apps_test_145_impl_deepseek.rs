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
proof fn lemma_count_distinct_properties(s: Seq<char>)
    ensures count_distinct(s) == s.to_set().len() as int,
            count_distinct(s) % 2 == 0 || count_distinct(s) % 2 == 1
{
    assert(s.to_set().len() == s.to_set().len());
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
    let username_seq = input@.subrange(0, input@.len() - 1);
    let mut char_set = Set::<char>::empty();
    let mut i: usize = 0;
    
    ghost {
        lemma_count_distinct_properties(username_seq);
    }
    
    while i < input.len() - 1
        invariant
            i >= 0,
            i <= input.len() - 1,
            char_set =s= username_seq.subrange(0, i as int).to_set()
        decreases (input.len() - 1) - i
    {
        char_set = char_set.insert(input[i]);
        i = i + 1;
    }
    
    let distinct_count = char_set.len() as i32;
    
    if distinct_count % 2 == 1 {
        vec!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n']
    } else {
        vec!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n']
    }
}
// </vc-code>


}

fn main() {}