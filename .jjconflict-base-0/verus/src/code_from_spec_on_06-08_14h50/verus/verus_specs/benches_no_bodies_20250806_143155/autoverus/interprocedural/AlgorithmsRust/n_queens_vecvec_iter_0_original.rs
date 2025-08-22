/*
This is an attempt of turning the following N Queens Rust implementation into Verus
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/n_queens.rs

A couple of notes:
1. A couple of features related to Vec<Vec<...>> are currently not supported by Verus 
 let  board = vec![vec!['.'; n]; n];
 board[row][col] = c;
As a result, I used a nested loop to implement board = vec![vec!['.'; n]; n]
And, I had to put board[row][col] = c into a Verus external function

2. The reading of board[row][col] *is* supported by Verus.
In fact, Verus would check buffer overflow at both levels/dimensions.
As a result, it takes a lot of specification to prove the free of buffer overflows, 
much more spec than proving free of overflow in a one-dimensional Vec.

3. There actually ARE arithmetic overflow in the original implementation.
 let mut j : i32 = col as i32 - (row as i32 - i as i32);
 and
 let j = col + row - i;
 in the is_safe function

 I added the board.len() < 1000 constraint so that Verus won't complain about arithmetic overflow.
*/

use vstd::prelude::*;
 
verus!{

    pub fn main () {
    // TODO: Remove this comment and implement the function body
    }

    

    #[verifier::external_body]
	fn myVecClone(v: &Vec<Vec<char>>) -> Vec<Vec<char>> {
    return Vec::new();  // TODO: Remove this line and implement the function body
	}

    #[verifier::external_body]
    pub fn setBoard(board: &mut Vec<Vec<char>>, row: usize, col: usize, c: char) 
    requires
        row < old(board).len(),
        col < old(board).len(),
    ensures
        board.len() == old(board).len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == old(board)@.index(i as int).len(),
    {
    // TODO: Remove this comment and implement the function body
    }

    pub fn readBoard(board: &Vec<Vec<char>>, row: usize, col: usize) -> char 
    requires
        row < board.len(),
        col < board@.index(row as int).len(),
    {
    assume(false);  // TODO: Replace with appropriate return value of type char
    }

    pub fn init_board(board: &mut Vec<Vec<char>>, n: usize)
    requires
        old(board).len() == 0,
    ensures
        board.len() == n,
        forall |i : int| 0<= i < n ==> #[trigger] board@.index(i as int).len() == n,
    {
    // TODO: Remove this comment and implement the function body
    }

    pub fn n_queens_solver(n: usize) -> Vec<Vec<Vec<char>>> 
    requires
        n < 1000,//added by Shan to eliminate potential arithmetic overflow 
    {
    return Vec::new();  // TODO: Remove this line and implement the function body
    }
    
    fn is_safe(board: &Vec<Vec<char>>, row: usize, col: usize) -> bool 
    requires
        row < board.len(),
        col < board.len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == board.len(),
        board.len() < 1000,
    {
    return false;  // TODO: Remove this line and implement the function body
    }
    
    fn solve(board: &mut Vec<Vec<char>>, row: usize, solutions: &mut Vec<Vec<Vec<char>>>) 
    requires
        row <= old(board).len(),
        forall |i : int| 0<= i < old(board).len() ==> #[trigger] old(board)@.index(i as int).len() == old(board).len(),
        old(board).len() < 1000,
    ensures
        board.len() == old(board).len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == old(board)@.index(i as int).len(),
    {
    // TODO: Remove this comment and implement the function body
    }

}
