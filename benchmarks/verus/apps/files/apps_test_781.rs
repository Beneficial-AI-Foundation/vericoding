// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(input: Seq<Seq<char>>) -> bool {
    input.len() == 8 &&
    (forall|i: int| 0 <= i < 8 ==> input[i].len() == 8) &&
    (forall|i: int, j: int| 0 <= i < 8 && 0 <= j < 8 ==> input[i][j] == 'W' || input[i][j] == 'B')
}

spec fn has_alternating_row(row: Seq<char>) -> bool
    recommends row.len() == 8,
                forall|j: int| 0 <= j < 8 ==> row[j] == 'W' || row[j] == 'B'
{
    forall|k: int| 1 <= k < 8 ==> row[k] != row[k-1]
}

spec fn all_rows_have_alternating_pattern(input: Seq<Seq<char>>) -> bool
    recommends valid_input(input)
{
    forall|i: int| 0 <= i < 8 ==> has_alternating_row(input[i])
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<Seq<char>>) -> (result: Seq<char>)
    requires valid_input(input)
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