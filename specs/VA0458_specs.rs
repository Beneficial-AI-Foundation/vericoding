// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, k: int, h: Seq<int>) -> bool {
    n >= 1 && n == h.len() && m >= 0 && k >= 0 && 
    (forall|i: int| 0 <= i < h.len() ==> h[i] >= 0)
}

spec fn can_reach_end(n: int, m: int, k: int, h: Seq<int>) -> bool
{
    &&& valid_input(n, m, k, h)
    &&& simulate_game(0, m, n, k, h)
}

spec fn simulate_game(pos: int, blocks: int, n: int, k: int, h: Seq<int>) -> bool
    decreases n - pos
{
    &&& 0 <= pos < n
    &&& n == h.len()
    &&& k >= 0
    &&& blocks >= 0
    &&& (forall|i: int| 0 <= i < h.len() ==> h[i] >= 0)
    &&& if pos == n - 1 {
        true
    } else {
        let h1 = h[pos];
        let h2 = h[pos + 1];
        if h1 >= h2 {
            let new_blocks = if h2 >= k { blocks + (h1 - h2) + k } else { blocks + h1 };
            simulate_game(pos + 1, new_blocks, n, k, h)
        } else {
            if h2 > h1 + blocks + k {
                false
            } else {
                let new_blocks = 
                    if h2 <= k { blocks + h1 }
                    else if (h2 - h1) <= k { blocks + k - (h2 - h1) }
                    else { blocks - (h2 - h1 - k) };
                new_blocks >= 0 && simulate_game(pos + 1, new_blocks, n, k, h)
            }
        }
    }
}

spec fn valid_complete_input_format(input: Seq<char>) -> bool {
    input.len() > 0 && input[input.len() - 1] == '\n'
}

spec fn valid_output_format(output: Seq<char>, input: Seq<char>) -> bool {
    output.len() >= 0 && 
    (output.len() == 0 || output[output.len() - 1] == '\n') &&
    (forall|i: int| 0 <= i < output.len() ==> output[i] == 'Y' || output[i] == 'E' || output[i] == 'S' || output[i] == 'N' || output[i] == 'O' || output[i] == '\n')
}

spec fn correct_game_results(output: Seq<char>, input: Seq<char>) -> bool {
    true
}

spec fn output_matches_test_case_count(output: Seq<char>, input: Seq<char>) -> bool {
    true
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires 
        stdin_input.len() > 0,
        stdin_input[stdin_input.len() - 1] == '\n',
        valid_complete_input_format(stdin_input),
    ensures 
        result.len() >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] == 'Y' || result[i] == 'E' || result[i] == 'S' || result[i] == 'N' || result[i] == 'O' || result[i] == '\n',
        result.len() == 0 || result[result.len() - 1] == '\n',
        valid_output_format(result, stdin_input),
        correct_game_results(result, stdin_input),
        output_matches_test_case_count(result, stdin_input),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}