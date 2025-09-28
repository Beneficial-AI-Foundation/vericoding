// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<Seq<char>>) -> bool {
    input.len() == 8 &&
    (forall|i: int| 0 <= i < 8 ==> #[trigger] input[i].len() == 8) &&
    (forall|i: int, j: int| 0 <= i < 8 && 0 <= j < 8 ==> (#[trigger] input[i][j] == 'W' || #[trigger] input[i][j] == 'B'))
}

spec fn has_alternating_row(row: Seq<char>) -> bool {
    row.len() == 8 &&
    (forall|j: int| 0 <= j < 8 ==> (#[trigger] row[j] == 'W' || #[trigger] row[j] == 'B')) &&
    row[0] == 'W' &&
    row[1] == 'B' &&
    row[2] == 'W' &&
    row[3] == 'B' &&
    row[4] == 'W' &&
    row[5] == 'B' &&
    row[6] == 'W' &&
    row[7] == 'B'
}

spec fn all_rows_have_alternating_pattern(input: Seq<Seq<char>>) -> bool {
    valid_input(input) &&
    (forall|i: int| 0 <= i < 8 ==> has_alternating_row(#[trigger] input[i]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes needed, helper seems correct */
fn check_row(row: &Vec<char>) -> (result: bool)
    requires
        row.len() == 8,
        forall|j: int| 0 <= j < 8 ==> (row@[j] == 'W' || row@[j] == 'B'),
    ensures
        result <==> has_alternating_row(row@),
{
    row[0] == 'W' &&
    row[1] == 'B' &&
    row[2] == 'W' &&
    row[3] == 'B' &&
    row[4] == 'W' &&
    row[5] == 'B' &&
    row[6] == 'W' &&
    row[7] == 'B'
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(input@.map(|i, row: Vec<char>| row@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added a proof block to help Verus instantiate quantifiers from the precondition. */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < 8
        invariant
            0 <= i <= 8,
            valid_input(input@.map(|_idx, row: Vec<char>| row@)),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] == 'Y' <==> has_alternating_row(input@[j]@)),
        decreases 8 - i
    {
        proof {
            let spec_input = input@.map(|_idx, row: Vec<char>| row@);
            assert(spec_input[i as int].len() == 8);
            assert(forall|j: int| 0 <= j < 8 ==> (spec_input[i as int][j] == 'W' || spec_input[i as int][j] == 'B'));
        }

        let is_alternating = check_row(&input[i]);
        if is_alternating {
            result.push('Y');
        } else {
            result.push('N');
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}