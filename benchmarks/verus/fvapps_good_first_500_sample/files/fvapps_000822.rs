// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_sum(elements: Seq<i32>) -> int
    decreases elements.len()
{
    if elements.len() == 0 {
        0
    } else {
        elements[0] + seq_sum(elements.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_max_sequence_sum(n: usize, grid: Vec<Vec<i32>>) -> (result: i32)
    requires 
        n > 0,
        grid.len() == n,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == n,
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> -1000 <= grid[i][j] && grid[i][j] <= 1000,
    ensures
        result == -1 || (
            exists|elements: Seq<i32>| 
                #[trigger] elements.len() == n &&
                (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] elements[i] > #[trigger] elements[j]) &&
                result == seq_sum(elements)
        )
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