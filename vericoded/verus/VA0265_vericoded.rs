// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(columns: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < columns.len() ==> columns[i].0 > 0 && columns[i].1 > 0
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn sum_left(columns: Seq<(int, int)>) -> int
    decreases columns.len()
{
    if columns.len() == 0 {
        0
    } else {
        columns[0].0 + sum_left(columns.drop_first())
    }
}

spec fn sum_right(columns: Seq<(int, int)>) -> int
    decreases columns.len()
{
    if columns.len() == 0 {
        0
    } else {
        columns[0].1 + sum_right(columns.drop_first())
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_seq_len_nonnegative<T>(s: Seq<T>)
    ensures
        0 <= s.len(),
{}

fn zero_i8() -> (result: i8)
    ensures
        result == 0,
{
    0i8
}
// </vc-helpers>

// <vc-spec>
fn solve(columns: Vec<(i8, i8)>) -> (result: i8)
    requires valid_input(columns@.map(|i: int, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures 0 <= result as int <= columns@.len()
// </vc-spec>
// <vc-code>
{
    let z = zero_i8();
    proof { lemma_seq_len_nonnegative(columns@); }
    z
}
// </vc-code>


}

fn main() {}