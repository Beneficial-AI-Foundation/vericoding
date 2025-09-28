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
    /* code modified by LLM (iteration 5): Move modulo operation into proof block to avoid exec/ghost type issues */
    let username_len = input.len() - 1;
    let mut distinct_chars: Set<char> = Set::empty();
    let mut i: usize = 0;
    
    while i < username_len
        invariant
            i <= username_len,
            distinct_chars =~= input@.subrange(0, i as int).to_set(),
            valid_input(input@),
            username_len == input.len() - 1,
    {
        distinct_chars = distinct_chars.insert(input[i]);
        i = i + 1;
    }
    
    assert(distinct_chars =~= input@.subrange(0, username_len as int).to_set());
    
    let distinct_count = distinct_chars.len();
    
    let ghost username = input@.subrange(0, input@.len() - 1);
    let ghost is_odd: bool;
    proof {
        assert(distinct_chars =~= username.to_set());
        assert(distinct_count as int == count_distinct(username));
        is_odd = (count_distinct(username) % 2 == 1);
    }
    
    if distinct_count % 2 == 1 {
        let mut output = Vec::new();
        output.push('I');
        output.push('G');
        output.push('N');
        output.push('O');
        output.push('R');
        output.push('E');
        output.push(' ');
        output.push('H');
        output.push('I');
        output.push('M');
        output.push('!');
        output.push('\n');
        
        proof {
            assert(output@ == seq!['I', 'G', 'N', 'O', 'R', 'E', ' ', 'H', 'I', 'M', '!', '\n']);
            assert(distinct_count % 2 == 1);
            assert((distinct_count as int) % 2 == 1);
            assert(count_distinct(username) % 2 == 1);
            assert(correct_output(username, output@));
        }
        output
    } else {
        let mut output = Vec::new();
        output.push('C');
        output.push('H');
        output.push('A');
        output.push('T');
        output.push(' ');
        output.push('W');
        output.push('I');
        output.push('T');
        output.push('H');
        output.push(' ');
        output.push('H');
        output.push('E');
        output.push('R');
        output.push('!');
        output.push('\n');
        
        proof {
            assert(output@ == seq!['C', 'H', 'A', 'T', ' ', 'W', 'I', 'T', 'H', ' ', 'H', 'E', 'R', '!', '\n']);
            assert(distinct_count % 2 == 0);
            assert((distinct_count as int) % 2 == 0);
            assert(count_distinct(username) % 2 == 0);
            assert(correct_output(username, output@));
        }
        output
    }
}
// </vc-code>


}

fn main() {}