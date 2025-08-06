/*
This is another attempt of turning the following N Queens Rust implementation into Verus
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/n_queens.rs

There are several issues here:
1. Since Verus has various constraints in its support to vec<vec>, in this implemnetation, I flatterned Vec<vec> into Vec<>
However, this led to a LOT of trouble in non-linear arithmetic related verification.

2. Because of my use of vec<>, there is now a side-effect of potential arithmetic overflow of n*n
 I added the board.len() < 1000 constraint so that Verus won't complain about arithmetic overflow.
*/

use vstd::prelude::*;
//use vstd::string::*;
 
verus!{

    pub fn main () {
    // TODO: Remove this comment and implement the function body
    }

    pub fn readBoard(board: &Vec<char>, row: usize, col: usize, n: usize) -> char 
    requires
        board.len() == n * n,
        row < n,
        col < n,
        n < 1000,
    {
    assume(false);  // TODO: Replace with appropriate return value of type char
    }

    pub fn setBoard(board: &mut Vec<char>, row: usize, col: usize, n: usize, c: char) 
    requires
        old(board).len() == n * n,
        row < n,
        col < n,
        n < 1000,
    ensures
        board.len() == n * n,
    {
    // TODO: Remove this comment and implement the function body
    }

    #[verifier::external_body]
	fn myVecClone(v: &Vec<char>) -> Vec<char> {
    return Vec::new();  // TODO: Remove this line and implement the function body
	}

    pub fn init_board(board: &mut Vec<char>, n: usize)
    requires
        n < 1000,
        old(board).len() == 0,
    ensures
        board.len() == n*n,
    {
    // TODO: Remove this comment and implement the function body
    }

    pub fn n_queens_solver(n: usize) -> Vec<Vec<char>> 
    requires
        n < 1000,
    {
    return Vec::new();  // TODO: Remove this line and implement the function body
    }
    
    fn is_safe(board: &Vec<char>, row: usize, col: usize, n: usize) -> bool 
    requires
        board.len() == n * n,
        row < n,
        col < n,
        n < 1000, 
    {
    return false;  // TODO: Remove this line and implement the function body
    }
    
    fn solve(board: &mut Vec<char>, row: usize, solutions: &mut Vec<Vec<char>>, n: usize) 
    requires
        n < 1000,
        row <= n,
        old(board).len() == n * n,
    ensures
        board.len() == n*n,
    {
    // TODO: Remove this comment and implement the function body
    }

}
 
