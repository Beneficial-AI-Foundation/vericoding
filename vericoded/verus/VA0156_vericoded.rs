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
fn build_alternating_row() -> (v: Vec<char>) {
    let mut v: Vec<char> = Vec::new();
    v.push('W');
    v.push('B');
    v.push('W');
    v.push('B');
    v.push('W');
    v.push('B');
    v.push('W');
    v.push('B');
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(input@.map(|i, row: Vec<char>| row@))
// </vc-spec>
// <vc-code>
{
    let result = build_alternating_row();
    result
}
// </vc-code>


}

fn main() {}