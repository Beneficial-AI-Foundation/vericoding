// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_position(r: int, c: int) -> bool {
    1 <= r <= 8 && 1 <= c <= 8
}

spec fn rook_moves(r1: int, c1: int, r2: int, c2: int) -> int
    recommends valid_position(r1, c1) && valid_position(r2, c2)
{
    if r1 == r2 && c1 == c2 {
        0
    } else if r1 == r2 || c1 == c2 {
        1
    } else {
        2
    }
}

spec fn bishop_moves(r1: int, c1: int, r2: int, c2: int) -> int
    recommends valid_position(r1, c1) && valid_position(r2, c2)
{
    if r1 == r2 && c1 == c2 {
        0
    } else {
        let row_diff = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
        let col_diff = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
        if row_diff == col_diff {
            1
        } else if (r1 + c1) % 2 == (r2 + c2) % 2 {
            2
        } else {
            0
        }
    }
}

spec fn king_moves(r1: int, c1: int, r2: int, c2: int) -> int
    recommends valid_position(r1, c1) && valid_position(r2, c2)
{
    let row_diff = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
    let col_diff = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
    if row_diff >= col_diff { row_diff } else { col_diff }
}

spec fn valid_result(result: Seq<int>, r1: int, c1: int, r2: int, c2: int) -> bool
    recommends valid_position(r1, c1) && valid_position(r2, c2)
{
    result.len() == 3 &&
    result[0] == rook_moves(r1, c1, r2, c2) &&
    result[1] == bishop_moves(r1, c1, r2, c2) &&
    result[2] == king_moves(r1, c1, r2, c2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(r1: int, c1: int, r2: int, c2: int) -> (result: Vec<int>)
    requires valid_position(r1, c1) && valid_position(r2, c2)
    ensures valid_result(result@, r1, c1, r2, c2)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}