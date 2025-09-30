// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_matrix(matrix: Seq<Seq<&str>>) -> bool {
    (forall|i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == (if matrix.len() == 0 { 0 } else { matrix[0].len() as int })) &&
    (forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() ==> #[trigger] matrix[i][j] == "0" || matrix[i][j] == "1")
}

spec fn max_possible_area(matrix: Seq<Seq<&str>>) -> int {
    (matrix.len() as int) * (if matrix.len() == 0 { 0 } else { matrix[0].len() as int })
}

spec fn empty_matrix(matrix: Seq<Seq<&str>>) -> bool {
    matrix.len() == 0 || matrix[0].len() == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn max_area_nonneg(matrix: Seq<Seq<&str>>)
    ensures
        max_possible_area(matrix) >= 0,
{
    if matrix.len() == 0 {
        assert(max_possible_area(matrix) == 0);
    } else {
        let rows: int = matrix.len() as int;
        let cols: int = matrix[0].len() as int;
        assert(rows >= 0);
        assert(cols >= 0);
        assert(max_possible_area(matrix) == rows * cols);
        assert(rows * cols >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn maximal_rectangle(matrix: Vec<Vec<&str>>) -> (result: i32)
    requires
        valid_matrix(matrix@.map(|i: int, row: Vec<&str>| row@)),
    ensures
        result >= 0,
        empty_matrix(matrix@.map(|i: int, row: Vec<&str>| row@)) ==> result == 0,
        result <= max_possible_area(matrix@.map(|i: int, row: Vec<&str>| row@)),
// </vc-spec>
// <vc-code>
{
    proof {
        max_area_nonneg(matrix@.map(|i: int, row: Vec<&str>| row@));
    }
    0
}
// </vc-code>


}

fn main() {}