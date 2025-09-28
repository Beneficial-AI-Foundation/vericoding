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
fn solve(r1: i8, c1: i8, r2: i8, c2: i8) -> (result: Vec<i8>)
    requires valid_position(r1 as int, c1 as int) && valid_position(r2 as int, c2 as int)
    ensures valid_result(result@.map(|_idx: int, x: i8| x as int), r1 as int, c1 as int, r2 as int, c2 as int)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    
    // Calculate rook moves
    let rook_moves_val = if r1 == r2 && c1 == c2 {
        0i8
    } else if r1 == r2 || c1 == c2 {
        1i8
    } else {
        2i8
    };
    result.push(rook_moves_val);
    
    // Calculate bishop moves
    let row_diff = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
    let col_diff = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
    let bishop_moves_val = if r1 == r2 && c1 == c2 {
        0i8
    } else if row_diff == col_diff {
        1i8
    } else if ((r1 + c1) % 2) == ((r2 + c2) % 2) {
        2i8
    } else {
        0i8
    };
    result.push(bishop_moves_val);
    
    // Calculate king moves
    let king_moves_val = if row_diff >= col_diff { row_diff } else { col_diff };
    result.push(king_moves_val);
    
    assert(result@.len() == 3);
    assert(result@[0] as int == rook_moves(r1 as int, c1 as int, r2 as int, c2 as int));
    assert(result@[1] as int == bishop_moves(r1 as int, c1 as int, r2 as int, c2 as int));
    assert(result@[2] as int == king_moves(r1 as int, c1 as int, r2 as int, c2 as int));
    assert(result@.map(|_idx: int, x: i8| x as int).len() == 3);
    assert(result@.map(|_idx: int, x: i8| x as int)[0] == rook_moves(r1 as int, c1 as int, r2 as int, c2 as int));
    assert(result@.map(|_idx: int, x: i8| x as int)[1] == bishop_moves(r1 as int, c1 as int, r2 as int, c2 as int));
    assert(result@.map(|_idx: int, x: i8| x as int)[2] == king_moves(r1 as int, c1 as int, r2 as int, c2 as int));
    
    result
}
// </vc-code>


}

fn main() {}