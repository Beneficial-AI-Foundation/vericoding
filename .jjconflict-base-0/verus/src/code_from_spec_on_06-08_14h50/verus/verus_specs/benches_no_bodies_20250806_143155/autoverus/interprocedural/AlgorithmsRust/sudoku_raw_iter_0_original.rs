/*

This example is from Algorithm/Rust project.
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/sudoku.rs

The original test cases test_sudoku_correct and test_sudoku_incorrect cannot be easily convereted to verification properties.
Instead, the added proof helps to verify the program free of arithemtic overflow and buffer overflow.

The main function is essentially the test_sudoku_correct function without the two run-time asserts.

*/

use vstd::prelude::*;

 
verus!{

	fn main() {
    // TODO: Remove this comment and implement the function body
	}

	 
	pub struct Sudoku {
		board: [u8; 81],
	}
	
	impl Sudoku {
		pub fn new(board: [u8; 81]) -> Sudoku {
    assume(false);  // TODO: Replace with appropriate return value of type Sudoku
		}

		fn setcell(&mut self, x: usize, y: usize, val: u8) 
		{
    // TODO: Remove this comment and implement the function body
		}

		fn readcell(&self, x: usize, y: usize) -> u8 
		{
    assume(false);  // TODO: Replace with appropriate return value of type u8
		}

		fn find_empty_cell(&self) -> (ret: Option<(usize, usize)>) 
		{
    return None;  // TODO: Remove this line and implement the function body
		}

		fn check(&self, index_tuple: (usize, usize), value: u8) -> bool 
		{
    return false;  // TODO: Remove this line and implement the function body
		}
	
		pub fn solve(&mut self) -> bool {
    return false;  // TODO: Remove this line and implement the function body
		}
	}
}
     
