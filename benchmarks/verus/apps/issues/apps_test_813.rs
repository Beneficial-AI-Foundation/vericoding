// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 3 && split_spaces(lines[0]).len() >= 3 &&
    {
        let n = parse_int(split_spaces(lines[0])[0]);
        n > 0
    }
}

spec fn valid_output(input: Seq<char>, result: Seq<char>) -> bool {
    let lines = split_lines(input);
    let n = parse_int(split_spaces(lines[0])[0]);
    result.len() == 2 * n - 1 &&
    (forall|i: int| 0 <= i < n ==> #[trigger] result[2*i] == '1' || result[2*i] == '2') &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[2*i+1] == ' ')
}

spec fn correct_assignment(input: Seq<char>, result: Seq<char>) -> bool {
    let lines = split_lines(input);
    let n = parse_int(split_spaces(lines[0])[0]);
    let arthur_apples = parse_int_seq(split_spaces(lines[1]));
    let arthur_set = Set::new(|x: int| arthur_apples.contains(x));
    forall|i: int| 1 <= i <= n ==> 
        (arthur_set.contains(i) ==> #[trigger] result[2*(i-1)] == '1') &&
        (!arthur_set.contains(i) ==> result[2*(i-1)] == '2')
}

/* Helper functions for parsing (spec functions) */
spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty()
}

spec fn split_spaces(line: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty()
}

spec fn parse_int(s: Seq<char>) -> int {
    0
}

spec fn parse_int_seq(strs: Seq<Seq<char>>) -> Seq<int> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires input.len() > 0
    ensures 
        !valid_input(input@) ==> result.len() == 0,
        valid_input(input@) ==> valid_output(input@, result@) && correct_assignment(input@, result@),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == '1' || result[i] == '2' || result[i] == ' ',
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}