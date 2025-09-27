// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_x_in_row(row: Seq<char>) -> int {
    row.filter(|c: char| c == 'X').len() as int
}

spec fn total_x_count(board: Seq<Seq<char>>) -> int 
    decreases board.len()
{
    if board.len() == 0 {
        0
    } else {
        count_x_in_row(board[0]) + total_x_count(board.skip(1))
    }
}

spec fn count_valid_neighbors(board: Seq<Seq<char>>, i: int, j: int) -> int {
    (if i + 1 < board.len() && board[i + 1][j] == 'X' { 1 } else { 0 }) +
    (if i > 0 && board[i - 1][j] == 'X' { 1 } else { 0 }) +
    (if j + 1 < board[i].len() && board[i][j + 1] == 'X' { 1 } else { 0 }) +
    (if j > 0 && board[i][j - 1] == 'X' { 1 } else { 0 })
}

spec fn valid_board_spec(board: Seq<Seq<char>>) -> bool {
    true
}

fn count_battleships(board: &Vec<Vec<char>>) -> (result: usize)
    requires valid_board_spec(board@.map_values(|row: Vec<char>| row@)),
    ensures 
        (board@.len() == 0) ==> result == 0,
        (board@.len() == 1 && board@[0].len() == 0) ==> result == 0,
        result >= 0,
        (result as int) <= total_x_count(board@.map_values(|row: Vec<char>| row@)),
        (board@.len() == 1 && board@[0]@ == seq!['X']) ==> result == 1,
        forall|i: int, j: int| 
            0 <= i && i < board@.len() && 0 <= j && j < board@[i].len() && board@[i][j] == 'X'
            ==> count_valid_neighbors(board@.map_values(|row: Vec<char>| row@), i, j) <= 2
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
fn main() {
    // let test1 = vec![vec!['X', '.', '.', '.'], vec!['.', '.', '.', '.'], vec!['.', '.', '.', '.']];
    // println!("{}", count_battleships(&test1));
    
    // let test2 = vec![vec!['X', '.', '.', 'X'], vec!['.', '.', '.', 'X'], vec!['.', '.', '.', 'X']];
    // println!("{}", count_battleships(&test2));
    
    // let test3: Vec<Vec<char>> = vec![];
    // println!("{}", count_battleships(&test3));
}