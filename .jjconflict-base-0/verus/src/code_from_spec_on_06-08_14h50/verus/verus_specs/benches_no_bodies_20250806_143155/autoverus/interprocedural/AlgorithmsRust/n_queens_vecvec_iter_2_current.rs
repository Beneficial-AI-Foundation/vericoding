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

    pub fn main() {
    }

    #[verifier::external_body]
    fn myVecClone(v: &Vec<Vec<char>>) -> Vec<Vec<char>> {
        /* code modified by LLM (iteration 1): fixed ensures clause syntax */
        ensures result.len() == v.len() &&
            forall |i: int| 0 <= i < v.len() ==> result@[i] == v@[i]
        {
            v.clone()
        }
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
        board[row][col] = c;
    }

    pub fn readBoard(board: &Vec<Vec<char>>, row: usize, col: usize) -> char 
    requires
        row < board.len(),
        col < board@.index(row as int).len(),
    {
        board[row][col]
    }

    pub fn init_board(board: &mut Vec<Vec<char>>, n: usize)
    requires
        old(board).len() == 0,
    ensures
        board.len() == n,
        forall |i : int| 0<= i < n ==> #[trigger] board@.index(i as int).len() == n,
    {
        let mut i = 0;
        while i < n 
        invariant
            i <= n,
            board.len() == i,
            forall |j : int| 0 <= j < i ==> #[trigger] board@.index(j as int).len() == n,
        {
            let mut row = Vec::new();
            let mut j = 0;
            while j < n
            invariant
                j <= n,
                row.len() == j,
            {
                row.push('.');
                j += 1;
            }
            board.push(row);
            i += 1;
        }
    }

    pub fn n_queens_solver(n: usize) -> Vec<Vec<Vec<char>>> 
    requires
        n < 1000,//added by Shan to eliminate potential arithmetic overflow 
    {
        let mut board = Vec::new();
        init_board(&mut board, n);
        let mut solutions = Vec::new();
        solve(&mut board, 0, &mut solutions);
        solutions
    }
    
    fn is_safe(board: &Vec<Vec<char>>, row: usize, col: usize) -> bool 
    requires
        row < board.len(),
        col < board.len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == board.len(),
        board.len() < 1000,
    {
        // Check column
        let mut i = 0;
        while i < row
        invariant
            i <= row,
            row < board.len(),
            col < board.len(),
            forall |j : int| 0<= j < board.len() ==> #[trigger] board@.index(j as int).len() == board.len(),
        {
            if readBoard(board, i, col) == 'Q' {
                return false;
            }
            i += 1;
        }

        // Check diagonal (upper-left)
        let mut i = 0;
        while i < row
        invariant
            i <= row,
            row < board.len(),
            col < board.len(),
            forall |j : int| 0<= j < board.len() ==> #[trigger] board@.index(j as int).len() == board.len(),
        {
            let row_diff = row - i;
            if col >= row_diff {
                let check_col = col - row_diff;
                if readBoard(board, i, check_col) == 'Q' {
                    return false;
                }
            }
            i += 1;
        }

        // Check diagonal (upper-right)
        let mut i = 0;
        while i < row
        invariant
            i <= row,
            row < board.len(),
            col < board.len(),
            forall |j : int| 0<= j < board.len() ==> #[trigger] board@.index(j as int).len() == board.len(),
        {
            let row_diff = row - i;
            let check_col = col + row_diff;
            if check_col < board.len() {
                if readBoard(board, i, check_col) == 'Q' {
                    return false;
                }
            }
            i += 1;
        }

        true
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
        if row == board.len() {
            // Found a solution, add it to solutions
            let solution = myVecClone(board);
            solutions.push(solution);
            return;
        }

        let mut col = 0;
        while col < board.len()
        invariant
            row <= board.len(),
            col <= board.len(),
            board.len() == old(board).len(),
            forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == old(board)@.index(i as int).len(),
            old(board).len() < 1000,
        {
            if is_safe(board, row, col) {
                setBoard(board, row, col, 'Q');
                solve(board, row + 1, solutions);
                setBoard(board, row, col, '.');
            }
            col += 1;
        }
    }

}