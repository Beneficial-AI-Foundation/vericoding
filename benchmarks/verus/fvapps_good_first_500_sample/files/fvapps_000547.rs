// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn min_usize(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}

fn max_chess_subboard(n: usize, m: usize, board: Vec<Vec<u8>>, queries: Vec<usize>) -> (result: Vec<usize>)
    requires
        n > 0,
        m > 0,
        board.len() == n,
        forall|i: int| 0 <= i < board.len() ==> board[i].len() == m,
        queries.len() > 0,
        forall|i: int, j: int| 0 <= i < board.len() && 0 <= j < board[i].len() ==> (board[i][j] == 0 || board[i][j] == 1),
    ensures
        result.len() == queries.len(),
        forall|i: int| 0 <= i < result.len() ==> 1 <= result[i] && result[i] <= min_usize(n, m),
        forall|i: int, j: int| 0 <= i < j < result.len() && queries[i] <= queries[j] ==> result[i] <= result[j],
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