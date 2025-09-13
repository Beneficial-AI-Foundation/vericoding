// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(columns: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < columns.len() ==> columns[i].0 > 0 && columns[i].1 > 0
}

spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn sum_left(columns: Seq<(int, int)>) -> int
    decreases columns.len()
{
    if columns.len() == 0 {
        0
    } else {
        columns[0].0 + sum_left(columns.subrange(1, columns.len() as int))
    }
}

spec fn sum_right(columns: Seq<(int, int)>) -> int
    decreases columns.len()
{
    if columns.len() == 0 {
        0
    } else {
        columns[0].1 + sum_right(columns.subrange(1, columns.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(columns: Seq<(int, int)>) -> (result: int)
    requires valid_input(columns)
    ensures 0 <= result <= columns.len()
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}