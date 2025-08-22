use vstd::prelude::*;

verus!{

    pub fn main () {
        // Main function - can be empty as per specification
    }

    pub fn readBoard(board: &Vec<char>, row: usize, col: usize, n: usize) -> char 
    requires
        board.len() == n * n,
        row < n,
        col < n,
        n < 1000,
    {
        board[row * n + col]
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
        board.set(row * n + col, c);
    }

    #[verifier::external_body]
    fn myVecClone(v: &Vec<char>) -> Vec<char> {
        v.clone()
    }

    pub fn init_board(board: &mut Vec<char>, n: usize)
    requires
        n < 1000,
        old(board).len() == 0,
    ensures
        board.len() == n*n,
    {
        let mut i = 0;
        /* code modified by LLM (iteration 1): added decreases clause for termination proof */
        while i < n * n
            invariant
                board.len() == i,
                i <= n * n,
            decreases n * n - i
        {
            board.push('.');
            i = i + 1;
        }
    }

    pub fn n_queens_solver(n: usize) -> Vec<Vec<char>> 
    requires
        n < 1000,
    {
        let mut board = Vec::new();
        init_board(&mut board, n);
        let mut solutions = Vec::new();
        solve(&mut board, 0, &mut solutions, n);
        solutions
    }
    
    fn is_safe(board: &Vec<char>, row: usize, col: usize, n: usize) -> bool 
    requires
        board.len() == n * n,
        row < n,
        col < n,
        n < 1000, 
    {
        // Check column
        let mut i = 0;
        /* code modified by LLM (iteration 1): added decreases clause for termination proof */
        while i < row
            invariant
                i <= row,
                row < n,
                col < n,
                board.len() == n * n,
                n < 1000,
            decreases row - i
        {
            if readBoard(board, i, col, n) == 'Q' {
                return false;
            }
            i = i + 1;
        }
        
        // Check diagonal (upper left)
        let mut i = 0;
        /* code modified by LLM (iteration 1): added decreases clause for termination proof */
        while i < row && col >= i
            invariant
                i <= row,
                row < n,
                col < n,
                board.len() == n * n,
                n < 1000,
            decreases row - i
        {
            if col >= i && readBoard(board, row - i - 1, col - i, n) == 'Q' {
                return false;
            }
            i = i + 1;
        }
        
        // Check diagonal (upper right)
        let mut i = 0;
        /* code modified by LLM (iteration 1): added decreases clause for termination proof */
        while i < row && col + i < n
            invariant
                i <= row,
                row < n,
                col < n,
                board.len() == n * n,
                n < 1000,
            decreases row - i
        {
            if col + i < n && readBoard(board, row - i - 1, col + i, n) == 'Q' {
                return false;
            }
            i = i + 1;
        }
        
        true
    }
    
    fn solve(board: &mut Vec<char>, row: usize, solutions: &mut Vec<Vec<char>>, n: usize) 
    requires
        n < 1000,
        row <= n,
        old(board).len() == n * n,
    ensures
        board.len() == n*n,
    /* code modified by LLM (iteration 1): added decreases clause for termination proof of recursive calls */
    decreases n - row
    {
        if row == n {
            let solution = myVecClone(board);
            solutions.push(solution);
            return;
        }
        
        let mut col = 0;
        /* code modified by LLM (iteration 1): added decreases clause for termination proof */
        while col < n
            invariant
                board.len() == n * n,
                row < n,
                col <= n,
                n < 1000,
            decreases n - col
        {
            if is_safe(board, row, col, n) {
                setBoard(board, row, col, n, 'Q');
                solve(board, row + 1, solutions, n);
                setBoard(board, row, col, n, '.');
            }
            col = col + 1;
        }
    }

}