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
    let spec_username = input@.subrange(0, input@.len() - 1);

    let mut username = input;
    let len = username.len();
    username.truncate(len - 1);
    assert(username@ =~= spec_username);

    let mut seen: Vec<bool> = Vec::new();
    seen.resize(26, false);

    let mut distinct_count: u64 = 0;
    
    let mut i: usize = 0;
    while i < username.len()
        invariant
            0 <= i <= username.len(),
            username@ =~= spec_username,
            forall|j: int| 0 <= j < username@.len() ==> 'a' <= username@[j] && username@[j] <= 'z',
            seen.len() == 26,
            distinct_count as int == username@.subrange(0, i).to_set().len(),
            forall|c: char| 'a' <= c && c <= 'z' ==> 
                (seen@[(c as u8 - 'a' as u8) as int] <==> username@.subrange(0, i).to_set().contains(c)),
        decreases username.len() - i
    {
        let c = username[i];
        let idx = (c as u8 - 'a' as u8) as usize;
        
        if !seen[idx] {
            seen.set(idx, true);
            distinct_count = distinct_count + 1;
        }
        i = i + 1;
    }

    assert(distinct_count as int == count_distinct(spec_username));

    if distinct_count % 2 == 1 {
        return vec!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n'];
    } else {
        return vec!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n'];
    }
}
// </vc-code>


}

fn main() {}