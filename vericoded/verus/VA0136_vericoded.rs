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
/* helper modified by LLM (iteration 4): prove move counts are within 0..8 */
proof fn moves_bounds(r1: int, c1: int, r2: int, c2: int)
    requires
        valid_position(r1, c1) && valid_position(r2, c2),
    ensures
        0 <= rook_moves(r1, c1, r2, c2) && rook_moves(r1, c1, r2, c2) <= 8,
        0 <= bishop_moves(r1, c1, r2, c2) && bishop_moves(r1, c1, r2, c2) <= 8,
        0 <= king_moves(r1, c1, r2, c2) && king_moves(r1, c1, r2, c2) <= 8,
{
    // rook bounds
    if r1 == r2 && c1 == c2 {
        assert(rook_moves(r1, c1, r2, c2) == 0);
    } else if r1 == r2 || c1 == c2 {
        assert(rook_moves(r1, c1, r2, c2) == 1);
    } else {
        assert(rook_moves(r1, c1, r2, c2) == 2);
    }
    assert(0 <= rook_moves(r1, c1, r2, c2) && rook_moves(r1, c1, r2, c2) <= 8);

    // bishop bounds
    if r1 == r2 && c1 == c2 {
        assert(bishop_moves(r1, c1, r2, c2) == 0);
    } else {
        let row_diff = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
        let col_diff = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
        if row_diff == col_diff {
            assert(bishop_moves(r1, c1, r2, c2) == 1);
        } else if (r1 + c1) % 2 == (r2 + c2) % 2 {
            assert(bishop_moves(r1, c1, r2, c2) == 2);
        } else {
            assert(bishop_moves(r1, c1, r2, c2) == 0);
        }
    }
    assert(0 <= bishop_moves(r1, c1, r2, c2) && bishop_moves(r1, c1, r2, c2) <= 8);

    // king bounds
    let row_diff_k = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
    let col_diff_k = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
    assert(king_moves(r1, c1, r2, c2) == if row_diff_k >= col_diff_k { row_diff_k } else { col_diff_k });
    assert(0 <= king_moves(r1, c1, r2, c2) && king_moves(r1, c1, r2, c2) <= 8);
}

// </vc-helpers>

// <vc-spec>
fn solve(r1: i8, c1: i8, r2: i8, c2: i8) -> (result: Vec<i8>)
    requires valid_position(r1 as int, c1 as int) && valid_position(r2 as int, c2 as int)
    ensures valid_result(result@.map(|_idx: int, x: i8| x as int), r1 as int, c1 as int, r2 as int, c2 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute moves with i8 and prove correspondence in proof block */
    let rook: i8 = if r1 == r2 && c1 == c2 {
        0
    } else if r1 == r2 || c1 == c2 {
        1
    } else {
        2
    };

    let row_diff: i8 = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
    let col_diff: i8 = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
    let bishop: i8 = if r1 == r2 && c1 == c2 {
        0
    } else if row_diff == col_diff {
        1
    } else if ((r1 + c1) % 2) == ((r2 + c2) % 2) {
        2
    } else {
        0
    };

    let row_diff_k: i8 = if r1 >= r2 { r1 - r2 } else { r2 - r1 };
    let col_diff_k: i8 = if c1 >= c2 { c1 - c2 } else { c2 - c1 };
    let king: i8 = if row_diff_k >= col_diff_k { row_diff_k } else { col_diff_k };

    let mut v = Vec::new();
    v.push(rook);
    v.push(bishop);
    v.push(king);

    proof {
        let r1i: int = r1 as int;
        let c1i: int = c1 as int;
        let r2i: int = r2 as int;
        let c2i: int = c2 as int;

        moves_bounds(r1i, c1i, r2i, c2i);

        assert((rook as int) == rook_moves(r1i, c1i, r2i, c2i));
        assert((bishop as int) == bishop_moves(r1i, c1i, r2i, c2i));
        assert((king as int) == king_moves(r1i, c1i, r2i, c2i));
    }

    v
}

// </vc-code>


}

fn main() {}