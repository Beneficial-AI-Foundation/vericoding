// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> {
    seq![]
}

spec fn parse_int(s: Seq<char>) -> int {
    0
}

spec fn string_lt(a: Seq<char>, b: Seq<char>) -> bool {
    true
}

spec fn is_well_formed_input(stdin_input: Seq<char>) -> bool {
    let lines = split_lines(stdin_input);
    if lines.len() < 1 {
        false
    } else {
        let n = parse_int(lines[0]);
        n >= 0 && lines.len() >= n + 1 &&
        (forall|i: int| 1 <= i <= n && i < lines.len() ==> 
            lines[i].len() >= 1 && lines[i].len() <= 8 &&
            (forall|j: int| 0 <= j < lines[i].len() ==> 
                (lines[i][j] >= '0' && lines[i][j] <= '9') || lines[i][j] == '?'))
    }
}

spec fn has_valid_solution(stdin_input: Seq<char>) -> bool {
    let lines = split_lines(stdin_input);
    let n = parse_int(lines[0]);
    if n <= 0 {
        true
    } else {
        let input_strings = lines.subrange(1, n + 1);
        exists|solution: Seq<Seq<char>>| is_valid_sequence_solution(input_strings, solution)
    }
}

spec fn is_valid_sequence_solution(input: Seq<Seq<char>>, solution: Seq<Seq<char>>) -> bool {
    input.len() == solution.len() &&
    (forall|i: int| 0 <= i < input.len() ==> 
        input[i].len() == solution[i].len() &&
        forall|j: int| 0 <= j < input[i].len() ==> 
            (input[i][j] != '?' ==> input[i][j] == solution[i][j]) &&
            (input[i][j] == '?' ==> solution[i][j] >= '0' && solution[i][j] <= '9')) &&
    (forall|i: int| 0 <= i < solution.len() ==> is_valid_positive_integer(solution[i])) &&
    is_strictly_increasing_sequence(solution)
}

spec fn is_valid_positive_integer(s: Seq<char>) -> bool {
    s.len() >= 1 && 
    (forall|i: int| 0 <= i < s.len() ==> (s[i] >= '0' && s[i] <= '9')) &&
    (s.len() == 1 || s[0] != '0')
}

spec fn is_strictly_increasing_sequence(nums: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < nums.len() - 1 ==> is_lexicographically_smaller(nums[i], nums[i + 1])
}

spec fn is_lexicographically_smaller(a: Seq<char>, b: Seq<char>) -> bool {
    a.len() < b.len() || (a.len() == b.len() && string_lt(a, b))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        stdin_input@.len() > 0,
        is_well_formed_input(stdin_input@),
    ensures 
        result@.len() > 0,
        result@ == seq!['N', 'O', '\n'] || (result@.len() > 4 && result@.subrange(0, 4) == seq!['Y', 'E', 'S', '\n']),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}